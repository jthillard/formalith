//! The profiler window: records the evaluation of the lines, or everything while the application is used, then
//! shows the flamegraph of the recording and the time spent in each scope.

use std::collections::HashMap;

use eframe::egui::{self, RichText};

use super::{Frame, Lane, flamegraph};
use crate::protocol::WORKER_THREAD;

/// Seconds after which a recording of everything stops on its own.
const MAX_RECORDING: f64 = 30.;

/// The scopes shown in the table.
const MAX_ROWS: usize = 60;

/// The time spent in the scopes of a name in a lane.
struct Stat {
    lane: String,
    name: String,
    count: usize,
    /// The time spent in the outermost of nested scopes, in nanoseconds.
    total_ns: i64,
    /// The time spent in the scopes but not in their children, in nanoseconds.
    self_ns: i64,
}

/// What is being recorded.
#[derive(Clone, Copy)]
enum Recording {
    /// Everything, since a time.
    All(f64),
    /// The next evaluation, once sent.
    Armed,
    /// The evaluation of the request of a generation, or of newer ones replacing it.
    Evaluation(u64),
}

/// The profiler window, toggled with F12.
pub struct ProfilerWindow {
    /// Whether the window is shown.
    pub open: bool,
    recording: Option<Recording>,
    /// Whether the lines must be evaluated again, to profile their evaluation.
    evaluate: bool,
    /// Lanes received from the worker while recording.
    received: Vec<Lane>,
    /// The last recording.
    lanes: Vec<Lane>,
    /// Whether scopes of other crates (egui, wgpu...) are hidden.
    hide_internals: bool,
    /// The lanes shown, and the time spent in their scopes.
    shown: Vec<Lane>,
    stats: Vec<Stat>,
}

impl Default for ProfilerWindow {
    fn default() -> Self {
        Self {
            open: false,
            recording: None,
            evaluate: false,
            received: vec![],
            lanes: vec![],
            hide_internals: true,
            shown: vec![],
            stats: vec![],
        }
    }
}

/// Add the scopes of `lane` to the lane of the same name in `lanes`.
fn merge(lanes: &mut Vec<Lane>, lane: Lane) {
    let Some(into) = lanes.iter_mut().find(|into| into.name == lane.name) else {
        lanes.push(lane);
        return;
    };
    let offset = into.frames.len();
    into.frames.extend(lane.frames.into_iter().map(|mut frame| {
        for child in &mut frame.children {
            *child += offset;
        }
        frame
    }));
    into.roots
        .extend(lane.roots.iter().map(|root| root + offset));
}

/// Check if `frame` is a scope of Formalith, or a GPU span.
fn is_ours(frame: &Frame) -> bool {
    frame.file.is_empty() || frame.file.starts_with("formalith")
}

/// `lane` with only the scopes of Formalith, the others replaced by their children.
fn without_internals(lane: &Lane) -> Lane {
    /// Add the scope `i` of `lane` and its children to `out` inside `parent`, if kept.
    fn keep(lane: &Lane, i: usize, parent: Option<usize>, out: &mut Lane) {
        let frame = &lane.frames[i];
        let parent = if is_ours(frame) {
            let kept = Frame {
                children: vec![],
                ..frame.clone()
            };
            Some(out.push(kept, parent))
        } else {
            parent
        };
        for &child in &frame.children {
            keep(lane, child, parent, out);
        }
    }

    let mut out = Lane::new(lane.name.clone());
    for &root in &lane.roots {
        keep(lane, root, None, &mut out);
    }
    out
}

/// The time spent in each scope of `lanes`, sorted by decreasing self time.
fn stats(lanes: &[Lane]) -> Vec<Stat> {
    /// Count the scope `i` of `lane` and its children, inside the scopes named `open`.
    fn visit<'a>(
        lane: &'a Lane,
        i: usize,
        open: &mut Vec<&'a str>,
        stats: &mut HashMap<&'a str, Stat>,
    ) {
        let frame = &lane.frames[i];
        let duration = |frame: &Frame| frame.end_ns - frame.start_ns;
        let children: i64 = frame
            .children
            .iter()
            .map(|&c| duration(&lane.frames[c]))
            .sum();
        let stat = stats.entry(&frame.name).or_insert_with(|| Stat {
            lane: lane.name.clone(),
            name: frame.name.clone(),
            count: 0,
            total_ns: 0,
            self_ns: 0,
        });
        stat.count += 1;
        stat.self_ns += duration(frame) - children;
        if !open.contains(&frame.name.as_str()) {
            stat.total_ns += duration(frame);
        }
        open.push(&frame.name);
        for &child in &frame.children {
            visit(lane, child, open, stats);
        }
        open.pop();
    }

    let mut all = vec![];
    for lane in lanes {
        let mut stats = HashMap::new();
        for &root in &lane.roots {
            visit(lane, root, &mut vec![], &mut stats);
        }
        all.extend(stats.into_values());
    }
    all.sort_by_key(|stat| std::cmp::Reverse(stat.self_ns));
    all
}

impl ProfilerWindow {
    /// Check if it is recording, so that requests are recorded by the worker.
    #[must_use]
    pub const fn is_recording(&self) -> bool {
        self.recording.is_some()
    }

    /// Check if the lines must be evaluated again to profile their evaluation, once.
    pub const fn take_evaluate(&mut self) -> bool {
        std::mem::replace(&mut self.evaluate, false)
    }

    /// Add lanes recorded by the worker, to the recording, or to the last one if it stopped since.
    pub fn add_lanes(&mut self, lanes: Vec<Lane>) {
        let recording = self.is_recording();
        for lane in lanes {
            merge(
                if recording {
                    &mut self.received
                } else {
                    &mut self.lanes
                },
                lane,
            );
        }
        if !recording {
            self.refresh();
        }
    }

    /// The request of `generation` was sent: start profiling it if the next evaluation is awaited.
    pub fn request_sent(&mut self, generation: u64) {
        match self.recording {
            Some(Recording::Armed) => {
                // In the browser, the worker records itself
                #[cfg(not(target_arch = "wasm32"))]
                super::start();
                self.recording = Some(Recording::Evaluation(generation));
            }
            // It replaces the request being profiled
            Some(Recording::Evaluation(_)) => {
                self.recording = Some(Recording::Evaluation(generation));
            }
            _ => {}
        }
    }

    /// Every line of the request of `generation` was evaluated: stop if it is the one profiled.
    pub fn request_done(&mut self, generation: u64) {
        if let Some(Recording::Evaluation(profiled)) = self.recording
            && generation >= profiled
        {
            self.recording = None;
            // Natively, the worker's scopes wait for the end of the frame of the interface
            #[cfg(not(target_arch = "wasm32"))]
            let recorded = super::stop(true);
            #[cfg(target_arch = "wasm32")]
            let recorded = vec![];
            self.lanes = recorded
                .into_iter()
                .chain(std::mem::take(&mut self.received))
                .filter(|lane| lane.name == WORKER_THREAD)
                .collect();
            self.refresh();
        }
    }

    fn start(&mut self, now: f64) {
        super::start();
        self.recording = Some(Recording::All(now));
        self.received.clear();
    }

    /// Stop recording, keeping the recording of everything, dropping that of an evaluation.
    fn stop(&mut self) {
        let recording = self.recording.take();
        let lanes = super::stop(false);
        if matches!(recording, Some(Recording::All(_))) {
            self.lanes = lanes;
            for lane in std::mem::take(&mut self.received) {
                merge(&mut self.lanes, lane);
            }
            self.refresh();
        }
        self.received.clear();
    }

    /// Update the lanes shown and their statistics.
    fn refresh(&mut self) {
        self.shown = if self.hide_internals {
            self.lanes.iter().map(without_internals).collect()
        } else {
            self.lanes.clone()
        };
        self.stats = stats(&self.shown);
    }

    /// Show the window if it is open, handling F12.
    pub fn show(&mut self, ctx: &egui::Context, now: f64) {
        if ctx.input(|input| input.key_pressed(egui::Key::F12)) {
            self.open = !self.open;
        }
        if let Some(Recording::All(start)) = self.recording
            && now - start > MAX_RECORDING
        {
            self.stop();
        }
        let mut open = self.open;
        egui::Window::new("Profiler")
            .open(&mut open)
            .default_size([900., 520.])
            .vscroll(true)
            .show(ctx, |ui| self.contents(ui, now));
        self.open = open;
    }

    fn contents(&mut self, ui: &mut egui::Ui, now: f64) {
        ui.horizontal(|ui| {
            match self.recording {
                Some(Recording::All(start)) => {
                    if ui.button("Stop").clicked() {
                        self.stop();
                    } else {
                        ui.label(format!("Recording since {:.0} s…", now - start));
                    }
                }
                Some(Recording::Armed | Recording::Evaluation(_)) => {
                    if ui.button("Cancel").clicked() {
                        self.stop();
                    } else {
                        ui.spinner();
                        ui.label("Evaluating the lines…");
                    }
                }
                None => {
                    if ui
                        .button("Profile the evaluation")
                        .on_hover_text("Evaluate every line again, recording the worker")
                        .clicked()
                    {
                        self.recording = Some(Recording::Armed);
                        self.received.clear();
                        self.evaluate = true;
                        ui.ctx().request_repaint();
                    }
                    if ui
                        .button("Record")
                        .on_hover_text(
                            "Record everything until stopped: interface, evaluation and GPU",
                        )
                        .clicked()
                    {
                        self.start(now);
                    }
                }
            }
            if ui
                .checkbox(&mut self.hide_internals, "Only Formalith")
                .on_hover_text("Hide the scopes of egui, eframe and wgpu")
                .changed()
            {
                self.refresh();
            }
        });
        if self.shown.iter().all(|lane| lane.roots.is_empty()) {
            if !self.lanes.is_empty() {
                ui.weak("Nothing was recorded.");
            }
            return;
        }
        ui.separator();
        flamegraph::show(&self.shown, egui::Id::unique("profiler flamegraph"), ui);
        ui.add_space(8.);
        ui.collapsing("By scope", |ui| {
            egui::Grid::new("scopes").striped(true).show(ui, |ui| {
                for header in ["thread", "scope", "count", "total (ms)", "self (ms)"] {
                    ui.strong(header);
                }
                ui.end_row();
                #[allow(clippy::cast_precision_loss)]
                for stat in self.stats.iter().take(MAX_ROWS) {
                    ui.label(&stat.lane);
                    ui.label(RichText::new(&stat.name).monospace());
                    ui.label(stat.count.to_string());
                    ui.label(format!("{:.3}", stat.total_ns as f64 / 1e6));
                    ui.label(format!("{:.3}", stat.self_ns as f64 / 1e6));
                    ui.end_row();
                }
            });
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::protocol::{Request, RequestLine, Worker};

    /// The names of the scope `i` of `lane` and of its descendants.
    fn names(lane: &Lane, i: usize, out: &mut Vec<String>) {
        out.push(lane.frames[i].name.clone());
        for &child in &lane.frames[i].children {
            names(lane, child, out);
        }
    }

    #[test]
    fn test_profile_evaluation() {
        let _recording = super::super::tests::RECORDING
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut worker = Worker::new();
        let mut window = ProfilerWindow::default();
        // Twice, since profiling evaluates lines again instead of reusing their results
        for generation in 1..=2 {
            window.recording = Some(Recording::Armed);
            window.request_sent(generation);
            let request = Request {
                generation,
                set: "R".to_owned(),
                lines: vec![RequestLine {
                    id: 0,
                    text: "integrate(x*exp(x), x)".to_owned(),
                }],
                skip: vec![],
                profile: true,
            };
            worker = std::thread::Builder::new()
                .name(WORKER_THREAD.to_owned())
                .spawn(move || {
                    worker.evaluate(&request, |_| true);
                    worker
                })
                .unwrap()
                .join()
                .unwrap();
            window.request_done(generation);
            assert!(!window.is_recording());
            assert_eq!(window.shown.len(), 1);
            let lane = &window.shown[0];
            assert_eq!(lane.name, WORKER_THREAD);
            let mut all = vec![];
            for &root in &lane.roots {
                names(lane, root, &mut all);
            }
            assert!(all.iter().any(|name| name == "integrate"), "{all:?}");
            assert!(lane.frames.iter().all(is_ours));
            let line = lane
                .frames
                .iter()
                .find(|frame| frame.name == "line")
                .unwrap();
            assert_eq!(line.data, "integrate(x*exp(x), x)");
        }
    }

    #[test]
    fn test_without_internals() {
        let frame = |name: &str, file: &str| Frame {
            name: name.to_owned(),
            data: String::new(),
            file: file.to_owned(),
            start_ns: 0,
            end_ns: 1,
            children: vec![],
        };
        let mut lane = Lane::new("main");
        let ui = lane.push(frame("App::ui", "formalith-gui/src/app.rs"), None);
        let egui = lane.push(
            frame("Context::run", "egui-0.37.0/src/context.rs"),
            Some(ui),
        );
        lane.push(
            frame("Plotter::show", "formalith-gui/src/plot.rs"),
            Some(egui),
        );
        lane.push(frame("tessellate", "egui-0.37.0/src/context.rs"), None);
        let kept = without_internals(&lane);
        assert_eq!(kept.roots.len(), 1);
        let root = &kept.frames[kept.roots[0]];
        assert_eq!(root.name, "App::ui");
        assert_eq!(kept.frames[root.children[0]].name, "Plotter::show");
        assert_eq!(kept.frames.len(), 2);
    }
}
