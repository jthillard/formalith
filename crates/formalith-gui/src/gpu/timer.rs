//! GPU timestamps of the drawing of graphs and of the search of remarkable points, reported to the profiler
//! ([`crate::profiler::report_gpu`]) while it records (feature `profile`).
//!
//! Timestamps only give durations: spans are placed at the CPU time their work was prepared at, the first
//! timestamp of a batch being aligned on it. Graphs are drawn in egui's render pass, which needs timestamps inside
//! passes (native only); their queries are resolved in the encoder of the next frame and read back the frame after,
//! once that encoder is submitted.

use std::sync::{
    Arc,
    atomic::{AtomicU8, Ordering},
};

use eframe::egui_wgpu::wgpu;

/// The lane of the spans of graphs.
const GRAPHS: &str = "GPU graphs";

/// The lane of the spans of searches of remarkable points.
pub const ANALYSIS: &str = "GPU analysis";

/// Frames whose timestamps are in flight.
const SLOTS: usize = 3;

/// Graphs timed per frame.
const MAX_SPANS: u32 = 64;

/// Report spans from `timestamps`, pairs of little-endian `u64` ticks of `period` nanoseconds, named and with data
/// from `labels`, in `lane`, the first timestamp being at `anchor_ns`. Spans never written (zeros) are skipped.
pub fn report(
    lane: &'static str,
    labels: &[(&str, &str)],
    timestamps: &[u8],
    anchor_ns: i64,
    period: f32,
) {
    let ticks: Vec<u64> = timestamps
        .chunks_exact(8)
        .map(|bytes| u64::from_le_bytes(bytes.try_into().expect("8 bytes")))
        .collect();
    let spans: Vec<(&(&str, &str), u64, u64)> = labels
        .iter()
        .zip(ticks.chunks_exact(2))
        .filter(|(_, pair)| pair[0] != 0 && pair[1] >= pair[0])
        .map(|(label, pair)| (label, pair[0], pair[1]))
        .collect();
    let Some(first) = spans.iter().map(|(_, start, _)| *start).min() else {
        return;
    };
    #[allow(clippy::cast_possible_truncation, clippy::cast_precision_loss)]
    let time = |tick: u64| anchor_ns + ((tick - first) as f64 * f64::from(period)) as i64;
    for ((name, data), start, end) in spans {
        crate::profiler::report_gpu(lane, name, (*data).to_owned(), time(start), time(end));
    }
}

/// What a slot holds.
enum State {
    Free,
    /// The timestamps of a frame being drawn, with the label of each pair and the CPU time of the frame.
    Writing {
        labels: Vec<(u64, String)>,
        anchor_ns: i64,
    },
    /// Copied to the readback buffer in an encoder not submitted yet.
    Resolved {
        labels: Vec<(u64, String)>,
        anchor_ns: i64,
    },
    /// Being mapped: 0 while mapping, 1 once mapped, 2 on failure.
    Mapping {
        labels: Vec<(u64, String)>,
        anchor_ns: i64,
        status: Arc<AtomicU8>,
    },
}

/// The timestamps of a frame.
struct Slot {
    query_set: wgpu::QuerySet,
    resolve: wgpu::Buffer,
    readback: wgpu::Buffer,
    state: State,
}

/// Times the drawing of each graph.
pub struct RenderTimer {
    device: wgpu::Device,
    period: f32,
    slots: Vec<Slot>,
    /// The slot of the frame being drawn.
    writing: Option<usize>,
}

impl RenderTimer {
    /// A timer on `device`, `None` without timestamps inside passes.
    #[must_use]
    pub fn new(device: &wgpu::Device, queue: &wgpu::Queue) -> Option<Self> {
        let features =
            wgpu::Features::TIMESTAMP_QUERY | wgpu::Features::TIMESTAMP_QUERY_INSIDE_PASSES;
        if !device.features().contains(features) {
            return None;
        }
        let size = u64::from(2 * MAX_SPANS) * 8;
        let slots = (0..SLOTS)
            .map(|_| Slot {
                query_set: device.create_query_set(&wgpu::QuerySetDescriptor {
                    label: Some("graph timestamps"),
                    ty: wgpu::QueryType::Timestamp,
                    count: 2 * MAX_SPANS,
                }),
                resolve: device.create_buffer(&wgpu::BufferDescriptor {
                    label: Some("graph timestamps"),
                    size,
                    usage: wgpu::BufferUsages::QUERY_RESOLVE | wgpu::BufferUsages::COPY_SRC,
                    mapped_at_creation: false,
                }),
                readback: device.create_buffer(&wgpu::BufferDescriptor {
                    label: Some("graph timestamps"),
                    size,
                    usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
                    mapped_at_creation: false,
                }),
                state: State::Free,
            })
            .collect();
        Some(Self {
            device: device.clone(),
            period: queue.get_timestamp_period(),
            slots,
            writing: None,
        })
    }

    /// Start a frame: read the timestamps of earlier frames which are ready, resolve those of the last frame in
    /// `encoder`, and time this one if the profiler records.
    pub fn new_frame(&mut self, encoder: &mut wgpu::CommandEncoder) {
        let mapping = |slot: &Slot| matches!(&slot.state, State::Mapping { status, .. } if status.load(Ordering::Acquire) == 0);
        if self.slots.iter().any(mapping) {
            // Natively, callbacks are only called when polling
            let _ = self.device.poll(wgpu::PollType::Poll);
        }
        for slot in &mut self.slots {
            slot.state = match std::mem::replace(&mut slot.state, State::Free) {
                State::Mapping {
                    labels,
                    anchor_ns,
                    status,
                } => match status.load(Ordering::Acquire) {
                    0 => State::Mapping {
                        labels,
                        anchor_ns,
                        status,
                    },
                    1 => {
                        Self::read(slot, &labels, anchor_ns, self.period);
                        State::Free
                    }
                    _ => State::Free,
                },
                // Copied in the encoder of the last frame, which is submitted
                State::Resolved { labels, anchor_ns } => {
                    let status = Arc::new(AtomicU8::new(0));
                    let mapped = status.clone();
                    slot.readback
                        .map_async(wgpu::MapMode::Read, .., move |result| {
                            mapped.store(if result.is_ok() { 1 } else { 2 }, Ordering::Release);
                        });
                    State::Mapping {
                        labels,
                        anchor_ns,
                        status,
                    }
                }
                state => state,
            };
        }
        if let Some(index) = self.writing.take() {
            let slot = &mut self.slots[index];
            if let State::Writing { labels, anchor_ns } =
                std::mem::replace(&mut slot.state, State::Free)
                && !labels.is_empty()
            {
                #[allow(clippy::cast_possible_truncation)]
                let count = 2 * labels.len() as u32;
                encoder.resolve_query_set(&slot.query_set, 0..count, &slot.resolve, 0);
                encoder.copy_buffer_to_buffer(
                    &slot.resolve,
                    0,
                    &slot.readback,
                    0,
                    u64::from(count) * 8,
                );
                slot.state = State::Resolved { labels, anchor_ns };
            }
        }
        if crate::profiler::is_recording() {
            self.writing = self
                .slots
                .iter()
                .position(|slot| matches!(slot.state, State::Free));
            if let Some(index) = self.writing {
                self.slots[index].state = State::Writing {
                    labels: vec![],
                    anchor_ns: puffin::now_ns(),
                };
            }
        }
    }

    /// Report the timestamps of the mapped `slot`.
    fn read(slot: &Slot, labels: &[(u64, String)], anchor_ns: i64, period: f32) {
        {
            let Ok(data) = slot.readback.get_mapped_range(..) else {
                return;
            };
            let labels: Vec<(&str, &str)> = labels
                .iter()
                .map(|(_, label)| ("draw graph", label.as_str()))
                .collect();
            report(
                GRAPHS,
                &labels,
                &data[..labels.len() * 16],
                anchor_ns,
                period,
            );
        }
        slot.readback.unmap();
    }

    /// Time the graph `id` labeled `label` in this frame, if the profiler records and there is room.
    pub fn time(&mut self, id: u64, label: &str) {
        let Some(index) = self.writing else {
            return;
        };
        if let State::Writing { labels, .. } = &mut self.slots[index].state
            && labels.len() < MAX_SPANS as usize
            && !labels.iter().any(|(timed, _)| *timed == id)
        {
            labels.push((id, label.to_owned()));
        }
    }

    /// The query set and the index of the first of the two timestamps of the graph `id` in this frame, if timed.
    #[must_use]
    pub fn queries(&self, id: u64) -> Option<(&wgpu::QuerySet, u32)> {
        let slot = &self.slots[self.writing?];
        let State::Writing { labels, .. } = &slot.state else {
            return None;
        };
        let position = labels.iter().position(|(timed, _)| *timed == id)?;
        #[allow(clippy::cast_possible_truncation)]
        Some((&slot.query_set, 2 * position as u32))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gpu::tests::device;

    #[test]
    fn test_render_timer() {
        let Some((adapter, ..)) = device() else {
            eprintln!("No GPU, skipped");
            return;
        };
        let features =
            wgpu::Features::TIMESTAMP_QUERY | wgpu::Features::TIMESTAMP_QUERY_INSIDE_PASSES;
        if !adapter.features().contains(features) {
            eprintln!("No timestamps inside passes, skipped");
            return;
        }
        let descriptor = wgpu::DeviceDescriptor {
            required_features: features,
            ..Default::default()
        };
        let (device, queue) = pollster::block_on(adapter.request_device(&descriptor)).unwrap();
        let mut timer = RenderTimer::new(&device, &queue).unwrap();
        let texture = device.create_texture(&wgpu::TextureDescriptor {
            label: None,
            size: wgpu::Extent3d {
                width: 4,
                height: 4,
                depth_or_array_layers: 1,
            },
            mip_level_count: 1,
            sample_count: 1,
            dimension: wgpu::TextureDimension::D2,
            format: wgpu::TextureFormat::Rgba8Unorm,
            usage: wgpu::TextureUsages::RENDER_ATTACHMENT,
            view_formats: &[],
        });
        let view = texture.create_view(&wgpu::TextureViewDescriptor::default());
        let _recording = crate::profiler::tests::RECORDING
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        crate::profiler::start();
        // Timestamps written in the first frame, resolved in the second, mapped in the third and read in the last
        for frame in 0..4 {
            let mut encoder =
                device.create_command_encoder(&wgpu::CommandEncoderDescriptor::default());
            timer.new_frame(&mut encoder);
            if frame == 0 {
                timer.time(7, "y = x");
                let (query_set, index) = timer.queries(7).expect("Timed");
                let mut pass = encoder.begin_render_pass(&wgpu::RenderPassDescriptor {
                    label: None,
                    color_attachments: &[Some(wgpu::RenderPassColorAttachment {
                        view: &view,
                        depth_slice: None,
                        resolve_target: None,
                        ops: wgpu::Operations {
                            load: wgpu::LoadOp::Clear(wgpu::Color::TRANSPARENT),
                            store: wgpu::StoreOp::Store,
                        },
                    })],
                    depth_stencil_attachment: None,
                    timestamp_writes: None,
                    occlusion_query_set: None,
                    multiview_mask: None,
                });
                pass.write_timestamp(query_set, index);
                pass.write_timestamp(query_set, index + 1);
            }
            queue.submit([encoder.finish()]);
            let _ = device.poll(wgpu::PollType::wait_indefinitely());
        }
        let lanes = crate::profiler::stop(false);
        let lane = lanes
            .iter()
            .find(|lane| lane.name == GRAPHS)
            .expect("The graph is timed");
        assert_eq!(lane.frames.len(), 1);
        let span = &lane.frames[0];
        assert_eq!(
            (span.name.as_str(), span.data.as_str()),
            ("draw graph", "y = x")
        );
        assert!(span.start_ns <= span.end_ns);
    }
}
