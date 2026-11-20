//! The profiler window: records while the application is used, then shows the flamegraph of the recording and the
//! time spent in each scope.

use std::collections::HashMap;

use eframe::egui::{self, RichText};

use super::{Lane, flamegraph};

/// Seconds after which a recording stops on its own.
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

/// The profiler window, toggled with F12.
#[derive(Default)]
pub struct ProfilerWindow {
    /// Whether the window is shown.
    pub open: bool,
    /// When the recording started, if recording.
    recording: Option<f64>,
    /// Lanes received from the worker while recording.
    received: Vec<Lane>,
    /// The last recording.
    lanes: Vec<Lane>,
    stats: Vec<Stat>,
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
        let duration = |frame: &super::Frame| frame.end_ns - frame.start_ns;
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
    /// Check if it is recording, so that the worker should record too.
    #[must_use]
    pub const fn is_recording(&self) -> bool {
        self.recording.is_some()
    }

    /// Add lanes recorded by the worker, to the recording, or to the last one if it stopped since.
    pub fn add_lanes(&mut self, lanes: Vec<Lane>) {
        for lane in lanes {
            if self.is_recording() {
                merge(&mut self.received, lane);
            } else {
                merge(&mut self.lanes, lane);
            }
        }
        if !self.is_recording() {
            self.stats = stats(&self.lanes);
        }
    }

    fn start(&mut self, now: f64) {
        super::start();
        self.recording = Some(now);
        self.received.clear();
    }

    fn stop(&mut self) {
        self.recording = None;
        self.lanes = super::stop(false);
        for lane in std::mem::take(&mut self.received) {
            merge(&mut self.lanes, lane);
        }
        self.stats = stats(&self.lanes);
    }

    /// Show the window if it is open, handling F12.
    pub fn show(&mut self, ctx: &egui::Context, now: f64) {
        if ctx.input(|input| input.key_pressed(egui::Key::F12)) {
            self.open = !self.open;
        }
        if self
            .recording
            .is_some_and(|start| now - start > MAX_RECORDING)
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
            if let Some(start) = self.recording {
                if ui.button("Stop").clicked() {
                    self.stop();
                } else {
                    ui.label(format!("Recording since {:.0} s…", now - start));
                }
            } else {
                if ui.button("Record").clicked() {
                    self.start(now);
                }
                ui.weak(
                    "Use the application while recording, then stop. Drag and scroll to explore.",
                );
            }
        });
        if self.lanes.is_empty() {
            return;
        }
        ui.separator();
        flamegraph::show(&self.lanes, egui::Id::unique("profiler flamegraph"), ui);
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
