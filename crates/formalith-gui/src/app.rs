//! The application: a list of lines with their results and parameters, next to the plot of their graphs, in 2D or
//! in 3D.

use std::collections::{BTreeMap, HashMap};

use eframe::egui::{self, Color32, RichText, TextEdit, TextStyle};
use formalith_session::graph::{Graph, GraphKind};
use serde::{Deserialize, Serialize};

use crate::{
    evaluator::{BackendFactory, Evaluator},
    gpu,
    plot::{ComplexView, Drawable, Plotter},
    protocol::{LineResult, Reply, Request, RequestLine, ResultKind},
    space::{Space, is_surface},
    typeset::Typesetter,
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
const EXAMPLES: [&str; 13] = [
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
    "z = sin(x)*cos(y)",
];

/// The key of the state saved between sessions.
const STORAGE_KEY: &str = "formalith";

/// A line of input.
#[derive(Clone, Debug, Serialize, Deserialize)]
struct Line {
    id: u64,
    text: String,
    color: [u8; 3],
    visible: bool,
    /// How its graph is drawn when it is a function with complex values.
    #[serde(default)]
    complex_view: ComplexView,
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

/// The view of the graphs.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
enum PlotView {
    /// The 2D plot.
    #[default]
    Plane,
    /// The 3D view of the surfaces.
    Space,
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
    /// Whether results are typeset with Typst.
    typst: bool,
    view: PlotView,
}

impl Default for State {
    fn default() -> Self {
        let mut state = Self {
            lines: vec![],
            next_id: 0,
            params: BTreeMap::new(),
            set: "R".to_owned(),
            equal_aspect: true,
            typst: true,
            view: PlotView::Plane,
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
                complex_view: ComplexView::default(),
            },
        );
        id
    }

    /// Move the line at `from` so that it ends up at `to`.
    fn move_line(&mut self, from: usize, to: usize) {
        let line = self.lines.remove(from);
        self.lines.insert(to, line);
    }
}

/// A line being dragged by its handle.
#[derive(Clone, Copy)]
struct LineDrag {
    id: u64,
    /// The distance from the top of its frame to the point where it was grabbed.
    grab: f32,
    /// The height of its frame.
    height: f32,
    /// Its index among the other lines once dropped, where they leave a gap.
    to: usize,
}

/// The time the lines take to slide out of the way of a dragged line, in seconds.
const SLIDE_TIME: f32 = 0.1;

/// The identifier of the drag handle of the line `id`.
fn handle_id(id: u64) -> egui::Id {
    egui::Id::unique(("drag", id))
}

/// The height of the gap left for the dragged line `drag`.
fn gap_height_of(drag: Option<LineDrag>, spacing: f32) -> f32 {
    drag.map_or(0., |drag| drag.height + spacing)
}

/// The identifier of the animated gap left before the line `id`, or after the last line.
fn gap_id(id: Option<u64>) -> egui::Id {
    egui::Id::unique(("gap", id))
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
    /// Whether the lines were edited since they were last evaluated.
    edited: bool,
    results: HashMap<u64, Evaluated>,
    /// The images of the results.
    typesetter: Typesetter,
    plotter: Plotter,
    space: Space,
    /// The line whose curve shows its remarkable points.
    selected: Option<u64>,
    /// The line to give the keyboard focus.
    focus: Option<u64>,
    /// The line being dragged.
    drag: Option<LineDrag>,
    #[cfg(feature = "profile")]
    profiler: crate::profiler::ProfilerWindow,
}

impl App {
    /// The application, restoring the saved lines, evaluating them with backends from `backends`.
    #[must_use]
    pub fn new(cc: &eframe::CreationContext<'_>, backends: BackendFactory) -> Self {
        egui_extras::install_image_loaders(&cc.egui_ctx);
        let state = cc
            .storage
            .and_then(|storage| eframe::get_value(storage, STORAGE_KEY))
            .unwrap_or_default();
        let gpu = cc.wgpu_render_state.as_ref().map(gpu::install);
        Self {
            state,
            evaluator: Evaluator::new(backends),
            generation: 0,
            edited: true,
            results: HashMap::new(),
            typesetter: Typesetter::default(),
            plotter: Plotter::new(gpu),
            space: Space::new(gpu),
            selected: None,
            focus: None,
            drag: None,
            #[cfg(feature = "profile")]
            profiler: crate::profiler::ProfilerWindow::default(),
        }
    }

    /// Check if the profiler is recording, so that requests are recorded too.
    #[allow(clippy::unused_self)]
    const fn is_profiling(&self) -> bool {
        #[cfg(feature = "profile")]
        return self.profiler.is_recording();
        #[cfg(not(feature = "profile"))]
        false
    }

    /// Mark the lines as edited, to evaluate them at the next frame.
    const fn edit(&mut self) {
        self.edited = true;
    }

    /// Receive results, and send the lines to evaluate after an edit.
    fn evaluate(&mut self, ctx: &egui::Context, now: f64) {
        profile_scope!("App::evaluate");
        for reply in self.evaluator.poll(now) {
            match reply {
                Reply::Line {
                    generation,
                    id,
                    result,
                } => {
                    if let Some(graph) = &result.graph {
                        for param in &graph.params {
                            self.state.params.entry(param.clone()).or_default();
                        }
                    }
                    let new_surface = is_new_surface(
                        result.graph.as_ref(),
                        self.results
                            .get(&id)
                            .and_then(|evaluated| evaluated.result.graph.as_ref()),
                    );
                    self.results.insert(id, Evaluated { generation, result });
                    if new_surface && !self.has_flat_graph() {
                        self.state.view = PlotView::Space;
                    }
                }
                #[cfg(feature = "profile")]
                Reply::Profile { lanes } => self.profiler.add_lanes(lanes),
                #[cfg(feature = "profile")]
                Reply::Done { generation } => self.profiler.request_done(generation),
                #[cfg(not(feature = "profile"))]
                Reply::Done { .. } => {}
            }
        }
        if self.edited {
            self.edited = false;
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
                profile: self.is_profiling(),
            };
            self.evaluator.send(request, now);
            #[cfg(feature = "profile")]
            self.profiler.request_sent(self.generation);
        }
        if self.evaluator.is_busy() {
            // Check for stuck requests even without replies
            ctx.request_repaint_after(std::time::Duration::from_millis(500));
        }
    }

    /// Check if a visible line has a graph drawn only in the 2D plot.
    fn has_flat_graph(&self) -> bool {
        self.state
            .lines
            .iter()
            .filter(|line| line.visible)
            .any(|line| {
                self.results
                    .get(&line.id)
                    .and_then(|evaluated| evaluated.result.graph.as_ref())
                    .is_some_and(|graph| !is_surface(graph))
            })
    }

    /// Check if the result of the line `id` is outdated.
    fn is_pending(&self, id: u64) -> bool {
        self.edited
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
    fn lines_panel(&mut self, ui: &mut egui::Ui) {
        profile_scope!("App::lines_panel");
        ui.horizontal(|ui| {
            ui.heading("Formalith");
            ui.with_layout(egui::Layout::right_to_left(egui::Align::Center), |ui| {
                // Saved with egui's memory by eframe. Half circles, since the default fonts have no sun or moon
                // without the emoji fonts: only the monospace font, Hack, has these
                let (icon, hover, other) = match ui.ctx().theme() {
                    egui::Theme::Dark => ("◑", "Switch to the light theme", egui::Theme::Light),
                    egui::Theme::Light => ("◐", "Switch to the dark theme", egui::Theme::Dark),
                };
                if ui.add(egui::Button::new(RichText::new(icon).monospace()).frame(false)).on_hover_text(hover).clicked() {
                    ui.ctx().set_theme(other);
                }
                let response = ui.add(TextEdit::singleline(&mut self.state.set).desired_width(70.).hint_text("R"));
                if response.changed() {
                    self.edit();
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
                self.lines_list(ui);
                if ui.button("+ Add a line").clicked() {
                    let id = self.state.add_line(self.state.lines.len(), String::new());
                    self.focus = Some(id);
                }
                self.params_list(ui);
                ui.add_space(8.);
                ui.collapsing("Options", |ui| {
                    ui.checkbox(&mut self.state.equal_aspect, "Same scale on both axes");
                    ui.checkbox(&mut self.state.typst, "Typeset results with Typst");
                    if ui.button("Reset the view").clicked() {
                        self.plotter.reset_view();
                        self.space.reset_view();
                    }
                    #[cfg(feature = "profile")]
                    if ui.button("Profiler (F12)").clicked() {
                        self.profiler.open = !self.profiler.open;
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
                            self.edit();
                        }
                    }
                    ui.label("Products need `*`: `a*x`, not `a x` (`2x` is fine).");
                });
            });
    }

    /// The lines, with their results.
    fn lines_list(&mut self, ui: &mut egui::Ui) {
        let typst = self.state.typst;
        let mut remove = None;
        let mut insert = None;
        // The line to move, and its new index
        let mut moved = None;
        let ctx = ui.ctx().clone();
        // Drop the dragged line
        if let Some(drag) = self.drag
            && !ctx.is_being_dragged(handle_id(drag.id))
        {
            self.drag = None;
            if let Some(from) = self.state.lines.iter().position(|line| line.id == drag.id)
                && from != drag.to
            {
                self.state.move_line(from, drag.to);
                self.edit();
            }
        }
        let drag = self.drag;
        let slide = |id: egui::Id, gap: bool, height: f32| {
            let time = if drag.is_some() { SLIDE_TIME } else { 0. };
            ctx.animate_value_with_time(id, if gap { height } else { 0. }, time)
        };
        let spacing = ui.spacing().item_spacing.y;
        let gap_height = gap_height_of(drag, spacing);
        let (left, width) = (ui.cursor().left(), ui.available_width());
        // The tops the other lines would have without the dragged one and the gap, and where the gap would start
        // before each of them, then after the last one
        let mut tops = vec![];
        let mut top = ui.cursor().top();
        let mut started = None;
        let count = self.state.lines.len();
        for index in 0..count {
            let id = self.state.lines[index].id;
            let pending = self.is_pending(id);
            let evaluated = self.results.get(&id);
            let graph = evaluated.and_then(|evaluated| evaluated.result.graph.as_ref());
            let has_graph = graph.is_some();
            let is_complex_curve =
                graph.is_some_and(|graph| matches!(graph.kind, GraphKind::ComplexCurve { .. }));
            let only_in_space = self.state.view == PlotView::Plane
                && graph.is_some_and(|graph| matches!(graph.kind, GraphKind::Surface { .. }));
            let line = &mut self.state.lines[index];
            let selected = self.selected == Some(id);
            let dragged = drag.is_some_and(|drag| drag.id == id);
            let mut frame = egui::Frame::group(ui.style()).fill(if dragged {
                ui.visuals().panel_fill
            } else if selected {
                ui.visuals().faint_bg_color
            } else {
                Color32::TRANSPARENT
            });
            if dragged {
                frame = frame.shadow(ui.visuals().popup_shadow);
            }
            // A dragged line is drawn out of the list, on a layer of its own above the others, under the pointer;
            // the others leave a gap where it would go
            let mut floating = None;
            if let Some(drag) = drag {
                if dragged {
                    let pointer = ctx.pointer_interact_pos().map_or(top, |pointer| pointer.y);
                    floating = Some(
                        ui.new_child(
                            egui::UiBuilder::new()
                                .layer_id(egui::LayerId::new(
                                    egui::Order::Foreground,
                                    handle_id(id),
                                ))
                                .max_rect(egui::Rect::from_min_size(
                                    egui::pos2(left, pointer - drag.grab),
                                    egui::vec2(width, f32::INFINITY),
                                )),
                        ),
                    );
                } else {
                    let gap = slide(gap_id(Some(id)), drag.to == tops.len(), gap_height);
                    if gap > 0. {
                        ui.add_space(gap);
                    }
                    tops.push(top);
                }
            }
            let row = frame.show(floating.as_mut().unwrap_or(ui), |ui| {
                ui.horizontal(|ui| {
                    if drag_handle(ui, handle_id(id)).drag_started() {
                        started = Some(index);
                    }
                    ui.color_edit_button_srgb(&mut line.color);
                    if has_graph {
                        ui.checkbox(&mut line.visible, "")
                            .on_hover_text("Show the graph");
                    }
                    if is_complex_curve {
                        ui.selectable_value(&mut line.complex_view, ComplexView::Parts, "Re, Im")
                            .on_hover_text("Draw the real and imaginary parts (dimmer) as curves");
                        ui.selectable_value(&mut line.complex_view, ComplexView::Path, "path")
                            .on_hover_text("Draw the path of the values in the complex plane");
                    }
                    // Right to left, so that the line takes exactly the remaining width: a wider one would widen
                    // the panel, then the line again at the next frame.
                    ui.with_layout(egui::Layout::right_to_left(egui::Align::Center), |ui| {
                        if ui
                            .small_button("x")
                            .on_hover_text("Remove the line")
                            .clicked()
                        {
                            remove = Some(index);
                        }
                        let edit = TextEdit::singleline(&mut line.text)
                            .font(TextStyle::Monospace)
                            .desired_width(ui.available_width())
                            .hint_text("y = sin(x), f(x) := x^2, x^2 + y^2 < 1…")
                            .id_salt(("line", id));
                        let response = ui.add(edit);
                        if self.focus == Some(id) {
                            response.request_focus();
                            self.focus = None;
                        }
                        if response.changed() {
                            self.edited = true;
                        }
                        if response.gained_focus() || response.clicked() {
                            self.selected = Some(id);
                        }
                        if response.has_focus() {
                            ui.input_mut(|input| {
                                if index > 0
                                    && input.consume_key(egui::Modifiers::ALT, egui::Key::ArrowUp)
                                {
                                    moved = Some((index, index - 1));
                                } else if index + 1 < count
                                    && input.consume_key(egui::Modifiers::ALT, egui::Key::ArrowDown)
                                {
                                    moved = Some((index, index + 1));
                                }
                            });
                        }
                        if response.lost_focus()
                            && ui.input(|input| input.key_pressed(egui::Key::Enter))
                        {
                            insert = Some(index + 1);
                        }
                    });
                });
                if let Some(evaluated) = evaluated {
                    let result = &evaluated.result;
                    let image = result
                        .typst
                        .as_deref()
                        .filter(|_| typst)
                        .and_then(|source| self.typesetter.get(ui.ctx(), source));
                    result_label(ui, id, result, image, pending);
                    if only_in_space {
                        ui.weak("drawn in the 3D view");
                    }
                } else if !line.text.trim().is_empty() {
                    ui.horizontal(|ui| {
                        ui.spinner();
                        ui.weak("evaluating…");
                    });
                }
            });
            if !dragged {
                top += row.response.rect.height() + spacing;
            }
            if started == Some(index) {
                let rect = row.response.rect;
                let origin = ctx.input(|input| input.pointer.press_origin());
                self.drag = Some(LineDrag {
                    id,
                    grab: origin.map_or(0., |origin| origin.y - rect.top()),
                    height: rect.height(),
                    to: index,
                });
            }
        }
        if let Some(drag) = drag {
            let gap = slide(gap_id(None), drag.to == tops.len(), gap_height);
            ui.add_space(gap);
            tops.push(top);
            // The gap goes where the top of the dragged line is closest to
            if let Some(pointer) = ctx.pointer_interact_pos()
                && let Some(drag) = &mut self.drag
            {
                let y = pointer.y - drag.grab;
                drag.to = (0..tops.len())
                    .min_by(|&i, &j| (tops[i] - y).abs().total_cmp(&(tops[j] - y).abs()))
                    .unwrap_or(drag.to);
            }
        }
        // The gap opens at once where the line was taken from
        if let Some(index) = started {
            let next = self.state.lines.get(index + 1).map(|line| line.id);
            ctx.animate_value_with_time(gap_id(next), gap_height_of(self.drag, spacing), 0.);
        }
        if let Some((from, to)) = moved
            && remove.is_none()
            && insert.is_none()
        {
            self.state.move_line(from, to);
            self.edit();
        }
        if let Some(index) = remove {
            let line = self.state.lines.remove(index);
            self.results.remove(&line.id);
            self.edit();
        }
        self.typesetter.retain(
            ui.ctx(),
            self.results
                .values()
                .filter_map(|evaluated| evaluated.result.typst.as_deref()),
        );
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
                    complex_view: line.complex_view,
                })
            })
            .collect()
    }
}

/// The handle by which a line is dragged: two columns of three dots, painted rather than a glyph missing from the
/// default fonts.
fn drag_handle(ui: &mut egui::Ui, id: egui::Id) -> egui::Response {
    let (_, rect) = ui.allocate_space(egui::vec2(10., ui.spacing().interact_size.y));
    let response = ui
        .interact(rect, id, egui::Sense::drag())
        .on_hover_cursor(egui::CursorIcon::Grab)
        .on_hover_text("Drag to move the line (or Alt+↑ / Alt+↓ while editing it)");
    if response.dragged() {
        ui.ctx().set_cursor_icon(egui::CursorIcon::Grabbing);
    }
    let color = ui.visuals().weak_text_color();
    for column in [-2., 2.] {
        for row in [-4., 0., 4.] {
            ui.painter()
                .circle_filled(rect.center() + egui::vec2(column, row), 1.2, color);
        }
    }
    response
}

/// Check if `graph` is a surface, when the `previous` graph of its line wasn't.
fn is_new_surface(graph: Option<&Graph>, previous: Option<&Graph>) -> bool {
    let surface = |graph: Option<&Graph>| {
        graph.is_some_and(|graph| matches!(graph.kind, GraphKind::Surface { .. }))
    };
    surface(graph) && !surface(previous)
}

/// Show the result of a line, as its typeset `image` (URI and bytes) if given, faded while a newer one is computed.
fn result_label(
    ui: &mut egui::Ui,
    id: u64,
    result: &LineResult,
    image: Option<(String, egui::load::Bytes)>,
    pending: bool,
) {
    let mut text = RichText::new(&result.text).monospace();
    text = match result.kind {
        ResultKind::None => return,
        ResultKind::Error => text.color(ui.visuals().error_fg_color),
        ResultKind::Message => text.weak(),
        ResultKind::Result => text,
    };
    // Scrolled rather than wrapped, which would break pretty printed results, or extended, which would widen the
    // panel.
    egui::ScrollArea::horizontal()
        .id_salt(("result", id))
        .auto_shrink([false, true])
        .show(ui, |ui| {
            ui.horizontal(|ui| {
                if pending {
                    ui.spinner();
                }
                let sense = if result.plain.is_some() {
                    egui::Sense::click()
                } else {
                    egui::Sense::hover()
                };
                let response = if let Some((uri, bytes)) = image {
                    // White glyphs, tinted like strong text (the plain text color is a dim gray in the dark theme)
                    let image = egui::Image::from_bytes(uri, bytes)
                        .fit_to_original_size(1.)
                        .tint(ui.visuals().strong_text_color())
                        .sense(sense);
                    ui.add_enabled(!pending, image)
                } else {
                    ui.add_enabled(
                        !pending,
                        egui::Label::new(text)
                            .wrap_mode(egui::TextWrapMode::Extend)
                            .selectable(false)
                            .sense(sense),
                    )
                };
                if let Some(plain) = &result.plain {
                    copy_on_click(ui, id, &response, plain);
                }
            });
        });
    if let Some(name) = result.graph.as_ref().and_then(|graph| graph.unsupported()) {
        ui.colored_label(
            ui.visuals().warn_fg_color,
            format!("cannot plot: `{name}` has no numerical value"),
        );
    }
}

/// Copy `plain` (a result in Formalith syntax) when `response` is clicked, showing "copied" next to it for a
/// second.
fn copy_on_click(ui: &mut egui::Ui, id: u64, response: &egui::Response, plain: &str) {
    const SHOWN: f64 = 1.;
    let response = response
        .clone()
        .on_hover_cursor(egui::CursorIcon::Copy)
        .on_hover_text("Click to copy");
    let key = egui::Id::unique(("copied", id));
    let now = ui.input(|input| input.time);
    if response.clicked() {
        ui.ctx().copy_text(plain.to_owned());
        ui.data_mut(|data| data.insert_temp(key, now));
    }
    if let Some(copied) = ui.data(|data| data.get_temp::<f64>(key)) {
        if now - copied < SHOWN {
            ui.weak("copied");
            ui.ctx()
                .request_repaint_after(std::time::Duration::from_secs_f64(SHOWN - (now - copied)));
        } else {
            ui.data_mut(|data| data.remove::<f64>(key));
        }
    }
}

impl eframe::App for App {
    fn ui(&mut self, ui: &mut egui::Ui, _frame: &mut eframe::Frame) {
        profile_scope!("App::ui");
        let ctx = ui.ctx().clone();
        let now = ctx.input(|input| input.time);
        self.evaluate(&ctx, now);
        self.animate(&ctx);
        let ids: Vec<u64> = self.state.lines.iter().map(|line| line.id).collect();
        self.plotter.retain(&ids);
        self.space.retain(&ids);

        let narrow = ui.available_width() < 700.;
        let panel = if narrow {
            egui::Panel::bottom("lines").default_size(ui.available_height() * 0.4)
        } else {
            egui::Panel::left("lines").default_size(380.)
        };
        panel.resizable(true).show(ui, |ui| self.lines_panel(ui));
        egui::CentralPanel::default().show(ui, |ui| {
            ui.horizontal(|ui| {
                ui.selectable_value(&mut self.state.view, PlotView::Plane, "2D")
                    .on_hover_text("Curves, regions and points");
                ui.selectable_value(&mut self.state.view, PlotView::Space, "3D")
                    .on_hover_text(
                        "Surfaces z = f(x, y), and functions of z in C (height |f|, colored by arg f). Drag to \
                         rotate, right-drag to pan, scroll to zoom, double-click to reset",
                    );
            });
            let mut plotter = std::mem::take(&mut self.plotter);
            let mut space = std::mem::take(&mut self.space);
            let drawables = self.drawables();
            match self.state.view {
                PlotView::Plane => {
                    plotter.show(ui, &drawables, self.selected, self.state.equal_aspect);
                }
                PlotView::Space => space.show(ui, &drawables),
            }
            drop(drawables);
            self.plotter = plotter;
            self.space = space;
        });
        #[cfg(feature = "profile")]
        {
            self.profiler.show(&ctx, now);
            if self.profiler.take_evaluate() {
                self.edited = true;
            }
            // Natively, eframe ends the frames of puffin
            #[cfg(target_arch = "wasm32")]
            if crate::profiler::is_recording() {
                profiling::finish_frame!();
            }
        }
    }

    fn save(&mut self, storage: &mut dyn eframe::Storage) {
        eframe::set_value(storage, STORAGE_KEY, &self.state);
    }
}
