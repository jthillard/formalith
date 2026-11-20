//! The application: a list of lines with their results and parameters, next to the plot of their graphs.

use std::collections::{BTreeMap, HashMap};

use eframe::egui::{self, Color32, RichText, TextEdit, TextStyle};
use serde::{Deserialize, Serialize};

use crate::{
    evaluator::{BackendFactory, Evaluator},
    plot::{Drawable, Plotter},
    protocol::{LineResult, Reply, Request, RequestLine, ResultKind},
};

/// Colors given to new lines, in turn.
const PALETTE: [[u8; 3]; 6] = [
    [0xc7, 0x44, 0x40],
    [0x2d, 0x70, 0xb3],
    [0x38, 0x8c, 0x46],
    [0x60, 0x42, 0xa6],
    [0xfa, 0x7e, 0x19],
    [0x2a, 0x9d, 0x8f],
];

/// Inputs shown as examples.
const EXAMPLES: [&str; 12] = [
    "y = a*sin(b*x)",
    "f(x) := x^3 - 3*x",
    "y = f(x - 1) + 1",
    "x = y^2 - 2",
    "x^2 + y^2 = r^2",
    "y < exp(-x^2)",
    "integrate(exp(-x^2), x)",
    "(1, f(1))",
    "series(cos(x), x, 0, 8)",
    "x^3 - 2*x = 0",
    "tan(x)",
    "diff(x^x, x)",
];

/// Seconds without editing before lines are evaluated.
const DEBOUNCE: f64 = 0.25;

/// The key of the state saved between sessions.
const STORAGE_KEY: &str = "formalith";

/// A line of input.
#[derive(Clone, Debug, Serialize, Deserialize)]
struct Line {
    id: u64,
    text: String,
    color: [u8; 3],
    visible: bool,
}

/// A parameter of the graphs, with a slider.
#[derive(Clone, Debug, Serialize, Deserialize)]
struct Slider {
    value: f64,
    min: f64,
    max: f64,
    /// Whether the value moves on its own, and in which direction.
    playing: bool,
    forward: bool,
}

impl Default for Slider {
    fn default() -> Self {
        Self {
            value: 1.,
            min: -10.,
            max: 10.,
            playing: false,
            forward: true,
        }
    }
}

/// The state saved between sessions.
#[derive(Debug, Serialize, Deserialize)]
#[serde(default)]
struct State {
    lines: Vec<Line>,
    next_id: u64,
    params: BTreeMap<String, Slider>,
    set: String,
    equal_aspect: bool,
}

impl Default for State {
    fn default() -> Self {
        let mut state = Self {
            lines: vec![],
            next_id: 0,
            params: BTreeMap::new(),
            set: "R".to_owned(),
            equal_aspect: true,
        };
        for text in ["y = a*sin(x)", "x^2 + y^2 < 9"] {
            state.add_line(state.lines.len(), text.to_owned());
        }
        state
    }
}

impl State {
    /// Insert a line with `text` at `index`, returning its identifier.
    fn add_line(&mut self, index: usize, text: String) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        let color = PALETTE[usize::try_from(id).unwrap_or(0) % PALETTE.len()];
        self.lines.insert(
            index,
            Line {
                id,
                text,
                color,
                visible: true,
            },
        );
        id
    }
}

/// The result of a line, with the generation of the request it answers.
struct Evaluated {
    generation: u64,
    result: LineResult,
}

/// The application.
pub struct App {
    state: State,
    evaluator: Evaluator,
    /// The generation of the last request.
    generation: u64,
    /// When the lines were last edited, if they weren't evaluated since.
    edited: Option<f64>,
    results: HashMap<u64, Evaluated>,
    plotter: Plotter,
    /// The line whose curve shows its remarkable points.
    selected: Option<u64>,
    /// The line to give the keyboard focus.
    focus: Option<u64>,
}

impl App {
    /// The application, restoring the saved lines, evaluating them with backends from `backends`.
    #[must_use]
    pub fn new(cc: &eframe::CreationContext<'_>, backends: BackendFactory) -> Self {
        let state = cc
            .storage
            .and_then(|storage| eframe::get_value(storage, STORAGE_KEY))
            .unwrap_or_default();
        Self {
            state,
            evaluator: Evaluator::new(backends),
            generation: 0,
            edited: Some(f64::NEG_INFINITY),
            results: HashMap::new(),
            plotter: Plotter::default(),
            selected: None,
            focus: None,
        }
    }

    /// Mark the lines as edited, to evaluate them soon.
    const fn edit(&mut self, now: f64) {
        self.edited = Some(now);
    }

    /// Receive results, and send the lines to evaluate once editing pauses.
    fn evaluate(&mut self, ctx: &egui::Context, now: f64) {
        for reply in self.evaluator.poll(now) {
            if let Reply::Line {
                generation,
                id,
                result,
            } = reply
            {
                if let Some(graph) = &result.graph {
                    for param in &graph.params {
                        self.state.params.entry(param.clone()).or_default();
                    }
                }
                self.results.insert(id, Evaluated { generation, result });
            }
        }
        if let Some(edited) = self.edited {
            if now - edited >= DEBOUNCE {
                self.edited = None;
                self.generation += 1;
                let request = Request {
                    generation: self.generation,
                    set: self.state.set.trim().to_owned(),
                    lines: self
                        .state
                        .lines
                        .iter()
                        .map(|line| RequestLine {
                            id: line.id,
                            text: line.text.clone(),
                        })
                        .collect(),
                    skip: vec![],
                };
                self.evaluator.send(request, now);
            } else {
                ctx.request_repaint_after(std::time::Duration::from_secs_f64(DEBOUNCE));
            }
        }
        if self.evaluator.is_busy() {
            // Check for stuck requests even without replies
            ctx.request_repaint_after(std::time::Duration::from_millis(500));
        }
    }

    /// Check if the result of the line `id` is outdated.
    fn is_pending(&self, id: u64) -> bool {
        self.edited.is_some()
            || self
                .results
                .get(&id)
                .is_none_or(|evaluated| evaluated.generation < self.generation)
    }

    /// Move the playing parameters.
    fn animate(&mut self, ctx: &egui::Context) {
        let dt = f64::from(ctx.input(|input| input.stable_dt)).min(0.1);
        let mut playing = false;
        for slider in self
            .state
            .params
            .values_mut()
            .filter(|slider| slider.playing)
        {
            playing = true;
            // A whole range in 4 seconds
            let delta = (slider.max - slider.min) * dt / 4.;
            slider.value += if slider.forward { delta } else { -delta };
            if slider.value >= slider.max {
                slider.value = slider.max;
                slider.forward = false;
            } else if slider.value <= slider.min {
                slider.value = slider.min;
                slider.forward = true;
            }
        }
        if playing {
            ctx.request_repaint();
        }
    }

    /// The panel of lines, parameters and options.
    fn lines_panel(&mut self, ui: &mut egui::Ui, now: f64) {
        ui.horizontal(|ui| {
            ui.heading("Formalith");
            ui.with_layout(egui::Layout::right_to_left(egui::Align::Center), |ui| {
                let response = ui.add(TextEdit::singleline(&mut self.state.set).desired_width(70.).hint_text("R"));
                if response.changed() {
                    self.edit(now);
                }
                ui.label("set").on_hover_text(
                    "The set expressions are evaluated in, like R, C, Z/7 or M(Z). Graphs are drawn in R.",
                );
            });
        });
        ui.separator();
        egui::ScrollArea::vertical()
            .auto_shrink([false, false])
            .show(ui, |ui| {
                self.lines_list(ui, now);
                if ui.button("+ Add a line").clicked() {
                    let id = self.state.add_line(self.state.lines.len(), String::new());
                    self.focus = Some(id);
                }
                self.params_list(ui);
                ui.add_space(8.);
                ui.collapsing("Options", |ui| {
                    ui.checkbox(&mut self.state.equal_aspect, "Same scale on both axes");
                    if ui.button("Reset the view").clicked() {
                        self.plotter.reset_view();
                    }
                });
                ui.collapsing("Examples", |ui| {
                    ui.label("Click to add:");
                    for example in EXAMPLES {
                        if ui.link(RichText::new(example).monospace()).clicked() {
                            let id = self
                                .state
                                .add_line(self.state.lines.len(), example.to_owned());
                            self.selected = Some(id);
                            self.edit(now);
                        }
                    }
                    ui.label("Products need `*`: `a*x`, not `a x` (`2x` is fine).");
                });
            });
    }

    /// The lines, with their results.
    fn lines_list(&mut self, ui: &mut egui::Ui, now: f64) {
        let mut remove = None;
        let mut insert = None;
        for index in 0..self.state.lines.len() {
            let id = self.state.lines[index].id;
            let pending = self.is_pending(id);
            let result = self.results.get(&id).map(|evaluated| &evaluated.result);
            let has_graph = result.is_some_and(|result| result.graph.is_some());
            let line = &mut self.state.lines[index];
            let selected = self.selected == Some(id);
            let frame = egui::Frame::group(ui.style()).fill(if selected {
                ui.visuals().faint_bg_color
            } else {
                Color32::TRANSPARENT
            });
            frame.show(ui, |ui| {
                ui.horizontal(|ui| {
                    let mut color = Color32::from_rgb(line.color[0], line.color[1], line.color[2]);
                    if ui.color_edit_button_srgba(&mut color).changed() {
                        line.color = [color.r(), color.g(), color.b()];
                    }
                    if has_graph {
                        ui.checkbox(&mut line.visible, "")
                            .on_hover_text("Show the graph");
                    }
                    let width = ui.available_width() - 30.;
                    let edit = TextEdit::singleline(&mut line.text)
                        .font(TextStyle::Monospace)
                        .desired_width(width)
                        .hint_text("y = sin(x), f(x) := x^2, x^2 + y^2 < 1…")
                        .id_salt(("line", id));
                    let response = ui.add(edit);
                    if self.focus == Some(id) {
                        response.request_focus();
                        self.focus = None;
                    }
                    if response.changed() {
                        self.edited = Some(now);
                    }
                    if response.gained_focus() || response.clicked() {
                        self.selected = Some(id);
                    }
                    if response.lost_focus()
                        && ui.input(|input| input.key_pressed(egui::Key::Enter))
                    {
                        insert = Some(index + 1);
                    }
                    if ui
                        .small_button("x")
                        .on_hover_text("Remove the line")
                        .clicked()
                    {
                        remove = Some(index);
                    }
                });
                if let Some(result) = result {
                    result_label(ui, result, pending);
                } else if !line.text.trim().is_empty() {
                    ui.horizontal(|ui| {
                        ui.spinner();
                        ui.weak("evaluating…");
                    });
                }
            });
        }
        if let Some(index) = remove {
            let line = self.state.lines.remove(index);
            self.results.remove(&line.id);
            self.edit(now);
        }
        if let Some(index) = insert {
            let id = self.state.add_line(index, String::new());
            self.focus = Some(id);
            self.selected = Some(id);
        }
    }

    /// The sliders of the parameters used by visible graphs.
    fn params_list(&mut self, ui: &mut egui::Ui) {
        let mut used: Vec<String> = self
            .state
            .lines
            .iter()
            .filter(|line| line.visible)
            .filter_map(|line| self.results.get(&line.id)?.result.graph.as_ref())
            .flat_map(|graph| graph.params.iter().cloned())
            .collect();
        used.sort();
        used.dedup();
        if used.is_empty() {
            return;
        }
        ui.add_space(8.);
        ui.strong("Parameters");
        for name in used {
            let slider = self.state.params.entry(name.clone()).or_default();
            ui.horizontal(|ui| {
                ui.label(RichText::new(&name).monospace().strong());
                let play = if slider.playing { "Pause" } else { "Play" };
                if ui.small_button(play).on_hover_text("Animate").clicked() {
                    slider.playing = !slider.playing;
                }
                ui.add(
                    egui::Slider::new(&mut slider.value, slider.min..=slider.max)
                        .clamping(egui::SliderClamping::Never),
                );
            });
            ui.horizontal(|ui| {
                ui.add_space(24.);
                ui.weak("from");
                ui.add(egui::DragValue::new(&mut slider.min).speed(0.1));
                ui.weak("to");
                ui.add(egui::DragValue::new(&mut slider.max).speed(0.1));
                if slider.min >= slider.max {
                    slider.max = slider.min + 1.;
                }
            });
        }
    }

    /// The graphs to draw.
    fn drawables(&self) -> Vec<Drawable<'_>> {
        self.state
            .lines
            .iter()
            .filter(|line| line.visible)
            .filter_map(|line| {
                let evaluated = self.results.get(&line.id)?;
                let graph = evaluated.result.graph.as_ref()?;
                if graph.unsupported().is_some() {
                    return None;
                }
                let params = graph
                    .params
                    .iter()
                    .map(|name| {
                        self.state
                            .params
                            .get(name)
                            .map_or(1., |slider| slider.value)
                    })
                    .collect();
                Some(Drawable {
                    id: line.id,
                    revision: evaluated.generation,
                    graph,
                    color: Color32::from_rgb(line.color[0], line.color[1], line.color[2]),
                    params,
                    name: line.text.clone(),
                })
            })
            .collect()
    }
}

/// Show the result of a line, faded while a newer one is computed.
fn result_label(ui: &mut egui::Ui, result: &LineResult, pending: bool) {
    let mut text = RichText::new(&result.text).monospace();
    text = match result.kind {
        ResultKind::None => return,
        ResultKind::Error => text.color(ui.visuals().error_fg_color),
        ResultKind::Message => text.weak(),
        ResultKind::Result => text,
    };
    ui.horizontal(|ui| {
        if pending {
            ui.spinner();
        }
        ui.add_enabled(
            !pending,
            egui::Label::new(text).wrap_mode(egui::TextWrapMode::Extend),
        );
    });
    if let Some(name) = result.graph.as_ref().and_then(|graph| graph.unsupported()) {
        ui.colored_label(
            ui.visuals().warn_fg_color,
            format!("cannot plot: `{name}` has no numerical value"),
        );
    }
}

impl eframe::App for App {
    fn ui(&mut self, ui: &mut egui::Ui, _frame: &mut eframe::Frame) {
        let ctx = ui.ctx().clone();
        let now = ctx.input(|input| input.time);
        self.evaluate(&ctx, now);
        self.animate(&ctx);
        let ids: Vec<u64> = self.state.lines.iter().map(|line| line.id).collect();
        self.plotter.retain(&ids);

        let narrow = ui.available_width() < 700.;
        let panel = if narrow {
            egui::Panel::bottom("lines").default_size(ui.available_height() * 0.4)
        } else {
            egui::Panel::left("lines").default_size(380.)
        };
        panel
            .resizable(true)
            .show(ui, |ui| self.lines_panel(ui, now));
        egui::CentralPanel::default().show(ui, |ui| {
            let mut plotter = std::mem::take(&mut self.plotter);
            let drawables = self.drawables();
            plotter.show(ui, &drawables, self.selected, self.state.equal_aspect);
            drop(drawables);
            self.plotter = plotter;
        });
    }

    fn save(&mut self, storage: &mut dyn eframe::Storage) {
        eframe::set_value(storage, STORAGE_KEY, &self.state);
    }
}
