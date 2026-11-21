//! Profiling of the interface, the evaluation and the GPU (feature `profile`), shown in [`ProfilerWindow`].
//!
//! Scopes are recorded with puffin, through the `profiling` crate whose scopes egui, eframe and wgpu already have, and
//! only while recording ([`start`], [`stop`]). Natively the worker is a thread of the same process, recorded like
//! the interface. In the browser it is another wasm instance: it records its own scopes and sends them with its
//! replies ([`crate::protocol::Reply::Profile`]). Both clocks count from the Unix epoch, so they line up. GPU
//! timestamps ([`crate::gpu::timer`]) are reported with [`report_gpu`], aligned on the CPU time their work was
//! submitted at.

#[cfg(feature = "ui")]
pub mod flamegraph;
#[cfg(feature = "ui")]
mod window;

use std::sync::{Arc, LazyLock, Mutex, Once};

#[cfg(feature = "ui")]
use eframe::egui_wgpu::{self, wgpu};
use puffin::{FrameData, GlobalProfiler, Reader, ScopeCollection, Stream};
use serde::{Deserialize, Serialize};

#[cfg(feature = "ui")]
pub use window::ProfilerWindow;

/// A recorded scope.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Frame {
    /// The name of the scope.
    pub name: String,
    /// Its dynamic data, like the line evaluated.
    pub data: String,
    /// The file of the scope, starting with its crate like `formalith/src/limit/mod.rs`, empty for GPU spans.
    #[serde(default)]
    pub file: String,
    /// Its start, in nanoseconds since the Unix epoch.
    pub start_ns: i64,
    /// Its end, in nanoseconds since the Unix epoch.
    pub end_ns: i64,
    /// The indices of the scopes inside it.
    pub children: Vec<usize>,
}

/// The scopes recorded on a thread, or a queue of the GPU.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Lane {
    /// The name of the thread.
    pub name: String,
    /// Its scopes.
    pub frames: Vec<Frame>,
    /// The indices of the outermost scopes.
    pub roots: Vec<usize>,
}

impl Lane {
    /// An empty lane named `name`.
    #[must_use]
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            ..Self::default()
        }
    }

    /// Add `frame` inside the scope `parent`, or as an outermost one, returning its index.
    pub fn push(&mut self, frame: Frame, parent: Option<usize>) -> usize {
        let index = self.frames.len();
        self.frames.push(frame);
        match parent {
            Some(parent) => self.frames[parent].children.push(index),
            None => self.roots.push(index),
        }
        index
    }

    /// The range of its scopes, if it has some.
    #[must_use]
    pub fn range_ns(&self) -> Option<(i64, i64)> {
        let start = self.roots.iter().map(|&i| self.frames[i].start_ns).min()?;
        let end = self.roots.iter().map(|&i| self.frames[i].end_ns).max()?;
        Some((start, end))
    }
}

/// The frames finished while recording.
static FRAMES: Mutex<Vec<Arc<FrameData>>> = Mutex::new(vec![]);

/// The scopes known so far, which frames only give the first time they are seen.
static SCOPES: LazyLock<Mutex<ScopeCollection>> = LazyLock::new(Mutex::default);

/// GPU spans reported while recording, by lane.
static GPU: Mutex<Vec<(&'static str, Frame)>> = Mutex::new(vec![]);

/// Check if scopes are recorded.
#[must_use]
pub fn is_recording() -> bool {
    puffin::are_scopes_on()
}

/// Start recording, forgetting what was recorded before.
pub fn start() {
    static SINK: Once = Once::new();
    SINK.call_once(|| {
        let mut profiler = GlobalProfiler::lock();
        // The scopes seen before the sink
        profiler.emit_scope_snapshot();
        profiler.add_sink(Box::new(|frame| {
            if let Ok(mut frames) = FRAMES.lock() {
                frames.push(frame);
            }
        }));
    });
    if let Ok(mut frames) = FRAMES.lock() {
        frames.clear();
    }
    if let Ok(mut gpu) = GPU.lock() {
        gpu.clear();
    }
    puffin::set_scopes_on(true);
}

/// Stop recording, returning the lanes recorded since [`start`]. Scopes still open are lost, as is the frame
/// being recorded unless `finish_frame`.
#[must_use]
pub fn stop(finish_frame: bool) -> Vec<Lane> {
    if finish_frame {
        GlobalProfiler::lock().new_frame();
    }
    puffin::set_scopes_on(false);
    let frames = FRAMES
        .lock()
        .map(|mut frames| std::mem::take(&mut *frames))
        .unwrap_or_default();
    let mut lanes = SCOPES
        .lock()
        .map(|mut scopes| lanes_from_puffin(&frames, &mut scopes))
        .unwrap_or_default();
    let gpu = GPU
        .lock()
        .map(|mut gpu| std::mem::take(&mut *gpu))
        .unwrap_or_default();
    for (name, frame) in gpu {
        let index = lanes
            .iter()
            .position(|lane| lane.name == name)
            .unwrap_or_else(|| {
                lanes.push(Lane::new(name));
                lanes.len() - 1
            });
        lanes[index].push(frame, None);
    }
    lanes
}

/// Report a span of GPU work named `name`, with `data`, in the lane `lane`, if recording.
pub fn report_gpu(lane: &'static str, name: &str, data: String, start_ns: i64, end_ns: i64) {
    if !is_recording() {
        return;
    }
    if let Ok(mut gpu) = GPU.lock() {
        gpu.push((
            lane,
            Frame {
                name: name.to_owned(),
                data,
                file: String::new(),
                start_ns,
                end_ns,
                children: vec![],
            },
        ));
    }
}

/// The lanes of the threads of `frames`, learning the scopes they introduce in `scopes`.
#[must_use]
pub fn lanes_from_puffin(frames: &[Arc<FrameData>], scopes: &mut ScopeCollection) -> Vec<Lane> {
    let mut lanes: Vec<Lane> = vec![];
    for frame in frames {
        for details in &frame.scope_delta {
            scopes.insert(details.clone());
        }
        #[allow(unreachable_patterns)]
        let unpacked = match frame.unpacked() {
            Ok(unpacked) => unpacked,
            Err(_) => continue,
        };
        for (thread, stream) in &unpacked.thread_streams {
            let name = if thread.name.is_empty() {
                "main"
            } else {
                &thread.name
            };
            let index = lanes
                .iter()
                .position(|lane| lane.name == name)
                .unwrap_or_else(|| {
                    lanes.push(Lane::new(name));
                    lanes.len() - 1
                });
            read_scopes(&stream.stream, 0, None, &mut lanes[index], scopes);
        }
    }
    lanes
}

/// Add the scopes of `stream` from `offset` to `lane`, inside `parent`.
fn read_scopes(
    stream: &Stream,
    offset: u64,
    parent: Option<usize>,
    lane: &mut Lane,
    scopes: &ScopeCollection,
) {
    let Ok(Ok(top)) = Reader::with_offset(stream, offset).map(Reader::read_top_scopes) else {
        return;
    };
    for scope in top {
        let details = scopes.fetch_by_id(&scope.id);
        let frame = Frame {
            name: details.map_or_else(|| "?".to_owned(), |details| details.name().to_string()),
            data: scope.record.data.to_owned(),
            file: details
                .map(|details| details.file_path.to_string())
                .unwrap_or_default(),
            start_ns: scope.record.start_ns,
            end_ns: scope.record.stop_ns(),
            children: vec![],
        };
        let index = lane.push(frame, parent);
        read_scopes(
            stream,
            scope.child_begin_position,
            Some(index),
            lane,
            scopes,
        );
    }
}

/// Request the GPU timestamps of [`crate::gpu::timer`] when creating the device of `options`, as far as the
/// adapter has them.
#[cfg(feature = "ui")]
pub fn request_timestamps(options: &mut egui_wgpu::WgpuConfiguration) {
    if let egui_wgpu::WgpuSetup::CreateNew(setup) = &mut options.wgpu_setup {
        let base = setup.device_descriptor.clone();
        setup.device_descriptor = Arc::new(move |adapter| {
            let mut descriptor = base(adapter);
            descriptor.required_features |= adapter.features()
                & (wgpu::Features::TIMESTAMP_QUERY | wgpu::Features::TIMESTAMP_QUERY_INSIDE_PASSES);
            descriptor
        });
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    /// Held by tests recording, since recording is global.
    pub static RECORDING: Mutex<()> = Mutex::new(());

    #[test]
    fn test_lanes_from_puffin() {
        let _recording = RECORDING
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        // Recorded on its own thread, so that its lane only has these scopes
        let frames = std::thread::Builder::new()
            .name("profiled".to_owned())
            .spawn(|| {
                start();
                {
                    profiling::scope!("outer", "data");
                    for _ in 0..2 {
                        profiling::scope!("inner");
                    }
                }
                stop(true)
            })
            .unwrap()
            .join()
            .unwrap();
        let lane = frames.iter().find(|lane| lane.name == "profiled").unwrap();
        assert_eq!(lane.roots.len(), 1);
        let outer = &lane.frames[lane.roots[0]];
        assert_eq!(
            (outer.name.as_str(), outer.data.as_str()),
            ("outer", "data")
        );
        assert_eq!(outer.children.len(), 2);
        let inner: Vec<&Frame> = outer.children.iter().map(|&i| &lane.frames[i]).collect();
        assert!(inner.iter().all(|frame| frame.name == "inner"));
        assert!(outer.start_ns <= inner[0].start_ns);
        assert!(inner[0].end_ns <= inner[1].start_ns);
        assert!(inner[1].end_ns <= outer.end_ns);
    }
}
