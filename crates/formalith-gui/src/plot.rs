//! Drawing of the graphs of the lines in an interactive plot. Curves, paths and the grids of complex maps are sampled
//! in `f64` on the CPU ([`crate::geometry`]) over a window around the view, sampled again when the view leaves it or
//! is zoomed, and drawn as lines; implicit relations and regions are plot items running their shader over the plot
//! ([`crate::gpu`]). Sequences are drawn as the points `(k, u_k)` of the integers `k` of the view. The remarkable points of the selected curve are searched on the CPU ([`crate::analysis`]).
//! Surfaces are drawn by the 3D view ([`crate::space`]) instead.

use std::{cell::RefCell, collections::HashMap, ops::RangeInclusive, sync::Arc};

use eframe::{
    egui::{self, Color32, Vec2b},
    egui_wgpu,
};
use egui_plot::{
    FilledArea, GridInput, HLine, HoverPosition, Line, MarkerShape, Plot, PlotBounds, PlotGeometry,
    PlotItem, PlotItemBase, PlotPoint, PlotTransform, PlotUi, Points, VLine,
};
use formalith_session::{
    formalith::field::{real::numeric::Numeric, sequence::numeric::NumericSequence},
    graph::{Comparison, Graph, GraphKind},
};

use crate::{
    analysis::{Kind, Point, intersections, remarkable_points},
    geometry::{GRID_K, Polyline, View, area, sample_function, sample_grid, sample_path},
    gpu::{GraphCallback, Shader, UNIFORMS},
    shader::{self, MAX_PARAMS},
};

/// A graph to draw.
pub struct Drawable<'a> {
    /// The identifier of its line.
    pub id: u64,
    /// Changes when the graph changes.
    pub revision: u64,
    /// The graph.
    pub graph: &'a Graph,
    /// The color of the line.
    pub color: Color32,
    /// The values of the parameters of the graph.
    pub params: Vec<f64>,
    /// The name shown when hovering it.
    pub name: String,
    /// How a [`GraphKind::ComplexCurve`] is drawn.
    pub complex_view: ComplexView,
}

/// How a [`GraphKind::ComplexCurve`] is drawn.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ComplexView {
    /// The curves of the real part and of the imaginary part (dimmer).
    #[default]
    Parts,
    /// The path `(Re f(t), Im f(t))` in the complex plane.
    Path,
}

/// The parts of the graph of a line, with their own shader or polylines: the only one of most graphs, or the
/// imaginary part or the path of a [`GraphKind::ComplexCurve`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Slot {
    Main,
    Imaginary,
    Path,
}

/// The zoom ratio past which polylines are sampled again.
const RESAMPLE_ZOOM: f64 = 1.5;

/// The segments of the path of a [`GraphKind::ComplexCurve`] before refinement.
const PATH_SEGMENTS: usize = 1024;

/// The view shown first and after a reset.
const DEFAULT_VIEW: View = View {
    x_min: -10.,
    x_max: 10.,
    y_min: -6.,
    y_max: 6.,
};

/// The width of lines, in points.
const LINE_WIDTH: f32 = 2.5;

/// The width of the axes, in points.
const AXIS_WIDTH: f32 = 1.5;

/// The spacing in points between the ticks of a step, along x and y, under which their labels are hidden and over
/// which they are opaque (egui_plot's defaults for its axes).
const TICK_SPACING: [(f32, f32); 2] = [(60., 80.), (20., 30.)];

/// The distance in points between a tick label and its axis, or the edge of the plot.
const TICK_GAP: f32 = 4.;

/// The period of dashes of strict boundaries, in points.
const DASH_PERIOD: f32 = 10.;

/// Distance in points from a graph under which it is hovered.
const HOVER_DISTANCE: f64 = 6.;
/// Largest number of points drawn for a sequence, beyond which one term out of several is drawn.
const MAX_SEQUENCE_POINTS: i64 = 2000;

/// What the remarkable points of the selected curve depend on, besides the view: its line, revision and
/// parameters, and those of the other curves.
type Content = Vec<u64>;

/// The range and number of samples of a search of remarkable points.
type Range = [u64; 3];

/// Families of polylines of a graph sampled on the CPU over a window around the view.
struct Sampled {
    /// The revision and the parameters of the line.
    key: Vec<u64>,
    window: View,
    /// The size of a pixel along x and y when sampled.
    pixel: [f64; 2],
    families: Vec<Vec<Polyline>>,
}

impl Sampled {
    /// Whether the polylines are still right for the line `key` in `view`, a pixel being `pixel` units.
    fn fits(&self, key: &[u64], view: &View, pixel: [f64; 2]) -> bool {
        self.key == key
            && self.window.contains(view)
            && (0..2).all(|i| {
                let ratio = pixel[i] / self.pixel[i];
                (1. / RESAMPLE_ZOOM..=RESAMPLE_ZOOM).contains(&ratio)
            })
    }
}

/// The interactive plot.
#[derive(Default)]
pub struct Plotter {
    /// Whether the GPU is set up, and colors are given in linear space.
    gpu: Option<bool>,
    /// The shaders of each line, with the revision they were made for.
    shaders: HashMap<(u64, Slot), (u64, Arc<Shader>)>,
    /// The polylines of each line.
    sampled: HashMap<(u64, Slot), Sampled>,
    /// The last points found.
    remarkable: Option<(Content, Range, Vec<Point>)>,
    frame: u64,
    reset: bool,
}

/// The values `[x, y, params...]` of an evaluation.
fn values(params: &[f64]) -> Vec<f64> {
    [f64::NAN, f64::NAN]
        .into_iter()
        .chain(params.iter().copied())
        .collect()
}

/// `expr` as a function of the variable `var` ([`Graph::X`] or [`Graph::Y`], the other one being undefined), with
/// the values `params` of its parameters.
fn function<'a>(expr: &'a Numeric, params: &[f64], var: usize) -> impl Fn(f64) -> f64 + 'a {
    let values = RefCell::new(values(params));
    move |t| {
        let mut values = values.borrow_mut();
        values[var] = t;
        expr.eval(&values)
    }
}

/// `expr` as a function of `x` and `y`, with the values `params` of its parameters.
fn function_xy<'a>(expr: &'a Numeric, params: &[f64]) -> impl Fn(f64, f64) -> f64 + 'a {
    let values = RefCell::new(values(params));
    move |x, y| {
        let mut values = values.borrow_mut();
        values[Graph::X] = x;
        values[Graph::Y] = y;
        expr.eval(&values)
    }
}

impl Plotter {
    /// The plot, drawing with the GPU if `gpu` is given ([`gpu::install`]), and colors in linear space if it is
    /// `true`.
    #[must_use]
    pub fn new(gpu: Option<bool>) -> Self {
        Self {
            gpu,
            ..Self::default()
        }
    }

    /// Go back to the default view.
    pub const fn reset_view(&mut self) {
        self.reset = true;
    }

    /// Forget the shaders and polylines of the lines which aren't in `ids`.
    pub fn retain(&mut self, ids: &[u64]) {
        self.shaders.retain(|(id, _), _| ids.contains(id));
        self.sampled.retain(|(id, _), _| ids.contains(id));
    }

    /// The shader `slot` of `drawable`, whose source is `source` when it changed.
    fn shader(
        &mut self,
        drawable: &Drawable<'_>,
        slot: Slot,
        source: impl FnOnce() -> String,
    ) -> Arc<Shader> {
        profile_scope!("Plotter::shader");
        match self.shaders.get(&(drawable.id, slot)) {
            Some((revision, shader)) if *revision == drawable.revision => shader.clone(),
            _ => {
                let shader = Shader::new(source());
                self.shaders
                    .insert((drawable.id, slot), (drawable.revision, shader.clone()));
                shader
            }
        }
    }

    /// The families of polylines of the slot `slot` of `drawable` in `view`, a pixel being `pixel` units, sampled
    /// again by `sample` over a window around the view when the graph changed, or the view left the window or was
    /// zoomed since.
    fn sampled(
        &mut self,
        drawable: &Drawable<'_>,
        slot: Slot,
        view: &View,
        pixel: [f64; 2],
        sample: impl FnOnce(&View, [f64; 2]) -> Vec<Vec<Polyline>>,
    ) -> &[Vec<Polyline>] {
        let key: Vec<u64> = std::iter::once(drawable.revision)
            .chain(drawable.params.iter().map(|value| value.to_bits()))
            .collect();
        let slot = (drawable.id, slot);
        if !self
            .sampled
            .get(&slot)
            .is_some_and(|sampled| sampled.fits(&key, view, pixel))
        {
            profile_scope!("sample", &drawable.name);
            let window = view.grown(1.);
            let families = sample(&window, pixel);
            self.sampled.insert(
                slot,
                Sampled {
                    key,
                    window,
                    pixel,
                    families,
                },
            );
        }
        &self.sampled[&slot].families
    }

    /// The polylines of the curve `y = expr(x)` of `drawable`, as its slot `slot`.
    fn curve(
        &mut self,
        drawable: &Drawable<'_>,
        slot: Slot,
        expr: &Numeric,
        view: &View,
        pixel: [f64; 2],
    ) -> &[Polyline] {
        &self.sampled(drawable, slot, view, pixel, |window, pixel| {
            let f = function(expr, &drawable.params, Graph::X);
            vec![sample_function(f, window, pixel)]
        })[0]
    }

    /// Show the plot of `drawables`, with the remarkable points of the curve of the line `selected` (roots, extrema,
    /// intersections with the other curves).
    pub fn show(
        &mut self,
        ui: &mut egui::Ui,
        drawables: &[Drawable<'_>],
        selected: Option<u64>,
        equal_aspect: bool,
    ) {
        profile_scope!("Plotter::show");
        self.frame += 1;
        let mut plot = Plot::new("plot")
            .default_x_bounds(DEFAULT_VIEW.x_min, DEFAULT_VIEW.x_max)
            .default_y_bounds(DEFAULT_VIEW.y_min, DEFAULT_VIEW.y_max)
            .auto_bounds(Vec2b::FALSE)
            .allow_double_click_reset(false)
            // The vertical scroll zooms (below) instead of panning.
            .allow_scroll([true, false])
            // The tick labels are drawn next to the axes (`paint_ticks`).
            .show_axes(false)
            .label_formatter(|position| match position {
                HoverPosition::NearDataPoint {
                    plot_name,
                    position,
                    ..
                } => Some(label(plot_name, position.x, position.y)),
                HoverPosition::Elsewhere { .. } => None,
            });
        if equal_aspect {
            plot = plot.data_aspect(1.);
        }
        let reset = std::mem::take(&mut self.reset);
        // The grid is drawn with the text color, dim in dark mode: the axes take the strong one there
        let visuals = ui.visuals();
        let axis = if visuals.dark_mode {
            visuals.strong_text_color().gamma_multiply(0.7)
        } else {
            visuals.text_color().gamma_multiply(0.6)
        };
        let response = plot.show(ui, |plot_ui| {
            if reset {
                plot_ui.set_plot_bounds(PlotBounds::from_min_max(
                    [DEFAULT_VIEW.x_min, DEFAULT_VIEW.y_min],
                    [DEFAULT_VIEW.x_max, DEFAULT_VIEW.y_max],
                ));
            }
            if plot_ui.response().contains_pointer() {
                let ctx = plot_ui.ctx();
                let speed = ctx.options(|options| options.input_options.scroll_zoom_speed);
                let scroll = ctx.input(|input| input.smooth_scroll_delta.y);
                if scroll != 0. {
                    plot_ui.zoom_bounds_around_hovered(egui::Vec2::splat((speed * scroll).exp()));
                }
            }
            let bounds = plot_ui.plot_bounds();
            if !(bounds.width() > 0. && bounds.height() > 0.) {
                return None;
            }
            // The axes, stronger than the grid lines at 0, below the graphs
            plot_ui.hline(
                HLine::new("", 0.)
                    .color(axis)
                    .width(AXIS_WIDTH)
                    .allow_hover(false),
            );
            plot_ui.vline(
                VLine::new("", 0.)
                    .color(axis)
                    .width(AXIS_WIDTH)
                    .allow_hover(false),
            );
            let view = View {
                x_min: bounds.min()[0],
                x_max: bounds.max()[0],
                y_min: bounds.min()[1],
                y_max: bounds.max()[1],
            };
            let frame = plot_ui.transform().frame();
            let pixels_per_point = plot_ui.ctx().pixels_per_point();
            let size = [
                f64::from(frame.width() * pixels_per_point),
                f64::from(frame.height() * pixels_per_point),
            ];
            let pixel = [view.width() / size[0], view.height() / size[1]];
            for drawable in drawables {
                self.draw(plot_ui, drawable, &view, pixel);
            }
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            self.draw_remarkable(plot_ui, drawables, selected, &view, size[0] as usize);
            let hovered = plot_ui
                .response()
                .hovered()
                .then(|| plot_ui.pointer_coordinate())
                .flatten()
                .and_then(|pointer| hover(drawables, pointer, plot_ui.transform()));
            if let Some((_, point)) = &hovered {
                plot_ui.points(
                    Points::new("", vec![*point])
                        .shape(MarkerShape::Circle)
                        .radius(3.5)
                        .filled(true)
                        .allow_hover(false)
                        .color(Color32::from_gray(110)),
                );
            }
            hovered
        });
        paint_ticks(ui, &response.transform);
        if let Some((name, [x, y])) = response.inner {
            response
                .response
                .on_hover_text_at_pointer(label(&name, x, y));
        }
    }

    /// Draw `drawable` in `view`, a pixel being `pixel` units.
    fn draw(
        &mut self,
        plot_ui: &mut PlotUi<'_>,
        drawable: &Drawable<'_>,
        view: &View,
        pixel: [f64; 2],
    ) {
        profile_scope!("Plotter::draw", &drawable.name);
        let params = &drawable.params;
        match &drawable.graph.kind {
            GraphKind::Function { expr, .. } => {
                let lines = self.curve(drawable, Slot::Main, expr, view, pixel);
                draw_lines(plot_ui, drawable, Slot::Main, lines, drawable.color);
            }
            GraphKind::Integral { expr, a, b, .. } => {
                let values = values(params);
                let (a, b) = (a.eval(&values), b.eval(&values));
                let lines = self.curve(drawable, Slot::Main, expr, view, pixel);
                // Without bounds, only the curve
                if !(a.is_nan() || b.is_nan()) {
                    let fill = drawable.color.gamma_multiply(0.25);
                    for (k, line) in lines.iter().enumerate() {
                        let points = area(line, a.min(b), a.max(b));
                        if points.len() < 2 {
                            continue;
                        }
                        let xs: Vec<f64> = points.iter().map(|point| point[0]).collect();
                        let low: Vec<f64> = points.iter().map(|point| point[1].min(0.)).collect();
                        let high: Vec<f64> = points.iter().map(|point| point[1].max(0.)).collect();
                        plot_ui.add(
                            FilledArea::new(drawable.name.clone(), &xs, &low, &high)
                                .id((drawable.id, "area", k))
                                .fill_color(fill)
                                .allow_hover(false),
                        );
                    }
                }
                draw_lines(plot_ui, drawable, Slot::Main, lines, drawable.color);
            }
            GraphKind::InverseFunction { expr } => {
                let families = self.sampled(drawable, Slot::Main, view, pixel, |window, pixel| {
                    let g = function(expr, params, Graph::Y);
                    let lines = sample_function(g, &window.transposed(), [pixel[1], pixel[0]]);
                    let swapped = lines
                        .into_iter()
                        .map(|line| line.into_iter().map(|[y, x]| [x, y]).collect())
                        .collect();
                    vec![swapped]
                });
                draw_lines(plot_ui, drawable, Slot::Main, &families[0], drawable.color);
            }
            GraphKind::Implicit { relations } => {
                let relations: Vec<(&Numeric, Comparison)> = relations
                    .iter()
                    .map(|relation| (&relation.expr, relation.relation))
                    .collect();
                self.draw_render(plot_ui, drawable, &relations);
            }
            GraphKind::Point { x, y } => {
                let values = values(params);
                let (x, y) = (x.eval(&values), y.eval(&values));
                if x.is_finite() && y.is_finite() {
                    plot_ui.points(
                        Points::new(drawable.name.clone(), vec![[x, y]])
                            .id(drawable.id)
                            .shape(MarkerShape::Circle)
                            .radius(5.)
                            .filled(true)
                            .color(drawable.color),
                    );
                }
            }
            GraphKind::Sequence { terms } => {
                let points = sequence_points(terms, params, view.x_min, view.x_max);
                plot_ui.points(
                    Points::new(drawable.name.clone(), points)
                        .id(drawable.id)
                        .shape(MarkerShape::Circle)
                        .radius(3.)
                        .filled(true)
                        .color(drawable.color),
                );
            }
            GraphKind::ComplexMap { re, im } => {
                let families = self.sampled(drawable, Slot::Main, view, pixel, |window, pixel| {
                    let (re, im) = (function_xy(re, params), function_xy(im, params));
                    Vec::from(sample_grid(|x, y| [re(x, y), im(x, y)], window, pixel))
                });
                // The lines `Re z = k` dimmer than the lines `Im z = k`
                draw_lines(plot_ui, drawable, Slot::Main, &families[0], drawable.color);
                let dim = drawable.color.gamma_multiply(0.5);
                draw_lines(plot_ui, drawable, Slot::Imaginary, &families[1], dim);
            }
            GraphKind::ComplexCurve { re, im, .. } => match drawable.complex_view {
                ComplexView::Parts => {
                    let lines = self.curve(drawable, Slot::Main, re, view, pixel);
                    draw_lines(plot_ui, drawable, Slot::Main, lines, drawable.color);
                    let lines = self.curve(drawable, Slot::Imaginary, im, view, pixel);
                    let dim = drawable.color.gamma_multiply(0.5);
                    draw_lines(plot_ui, drawable, Slot::Imaginary, lines, dim);
                }
                ComplexView::Path => {
                    let families =
                        self.sampled(drawable, Slot::Path, view, pixel, |window, pixel| {
                            let (re, im) = (
                                function(re, params, Graph::X),
                                function(im, params, Graph::X),
                            );
                            let end = f64::from(GRID_K);
                            let path = |t| [re(t), im(t)];
                            vec![sample_path(path, -end, end, PATH_SEGMENTS, window, pixel)]
                        });
                    draw_lines(plot_ui, drawable, Slot::Path, &families[0], drawable.color);
                }
            },
            // Drawn in the 3D view
            GraphKind::Surface { .. } => {}
        }
    }

    /// Draw the shader [`shader::render`] of `relations`, the graph of `drawable`.
    fn draw_render(
        &mut self,
        plot_ui: &mut PlotUi<'_>,
        drawable: &Drawable<'_>,
        relations: &[(&Numeric, Comparison)],
    ) {
        let Some(linear) = self.gpu else {
            return;
        };
        if drawable.params.len() > MAX_PARAMS {
            return;
        }
        let shader = self.shader(drawable, Slot::Main, || shader::render(relations));
        #[allow(clippy::cast_possible_truncation)]
        let params = drawable.params.iter().map(|value| *value as f32).collect();
        plot_ui.add(GpuGraph {
            base: PlotItemBase::new(drawable.name.clone()),
            id: drawable.id,
            frame: self.frame,
            shader,
            color: color(drawable.color, linear),
            fill: color(drawable.color.gamma_multiply(0.25), linear),
            params,
            drawable_color: drawable.color,
        });
    }

    /// Draw the remarkable points of the curve `selected` in `view`, searching them again on `pixels` pixels when it
    /// or the view changed.
    fn draw_remarkable(
        &mut self,
        plot_ui: &mut PlotUi<'_>,
        drawables: &[Drawable<'_>],
        selected: Option<u64>,
        view: &View,
        pixels: usize,
    ) {
        profile_scope!("Plotter::draw_remarkable");
        let Some(drawable) = drawables
            .iter()
            .find(|drawable| Some(drawable.id) == selected)
        else {
            return;
        };
        let Some((expr, derivative)) = curve(drawable.graph) else {
            return;
        };
        let others: Vec<&Drawable<'_>> = drawables
            .iter()
            .filter(|other| other.id != drawable.id && curve(other.graph).is_some())
            .collect();
        let mut content: Content = vec![];
        for curve in std::iter::once(drawable).chain(others.iter().copied()) {
            content.push(curve.id);
            content.push(curve.revision);
            content.extend(curve.params.iter().map(|value| value.to_bits()));
        }
        let samples = (pixels / 2).clamp(50, 1000);
        let (a, b) = (view.x_min, view.x_max);
        let range = [a.to_bits(), b.to_bits(), samples as u64];
        let current = self
            .remarkable
            .as_ref()
            .is_some_and(|(cached, cached_range, _)| *cached == content && *cached_range == range);
        if !current {
            profile_scope!("remarkable points", &drawable.name);
            let f = function(expr, &drawable.params, Graph::X);
            let derivative =
                derivative.map(|derivative| function(derivative, &drawable.params, Graph::X));
            let derivative = derivative
                .as_ref()
                .map(|derivative| derivative as &dyn Fn(f64) -> f64);
            let mut points = remarkable_points(&f, derivative, a, b, samples);
            for other in &others {
                if let Some((g, _)) = curve(other.graph) {
                    let g = function(g, &other.params, Graph::X);
                    points.extend(intersections(&f, &g, a, b, samples));
                }
            }
            self.remarkable = Some((content, range, points));
        }
        let Some((_, _, points)) = &self.remarkable else {
            return;
        };
        for kind in [Kind::Root, Kind::Minimum, Kind::Maximum, Kind::Intersection] {
            let series: Vec<[f64; 2]> = points
                .iter()
                .filter(|point| point.kind == kind)
                .map(|point| [point.x, point.y])
                .collect();
            if !series.is_empty() {
                plot_ui.points(
                    Points::new(kind.name(), series)
                        .shape(MarkerShape::Circle)
                        .radius(4.5)
                        .filled(true)
                        .color(Color32::from_gray(110)),
                );
            }
        }
    }
}

/// Draw the polylines `lines` of the slot `slot` of `drawable` in `color`.
fn draw_lines(
    plot_ui: &mut PlotUi<'_>,
    drawable: &Drawable<'_>,
    slot: Slot,
    lines: &[Polyline],
    color: Color32,
) {
    for (k, line) in lines.iter().enumerate() {
        plot_ui.line(
            Line::new(drawable.name.clone(), line.clone())
                .id((drawable.id, slot, k))
                .color(color)
                .width(LINE_WIDTH)
                // Bands (several points of a column as a vertical bar) make steep segments thinner
                .allow_band(false)
                .allow_hover(false),
        );
    }
}

/// The curve `y = f(x)` of `graph` with `f'`, if it has one.
const fn curve(graph: &Graph) -> Option<(&Numeric, Option<&Numeric>)> {
    match &graph.kind {
        GraphKind::Function { expr, derivative }
        | GraphKind::Integral {
            expr, derivative, ..
        } => Some((expr, derivative.as_ref())),
        _ => None,
    }
}

/// The premultiplied components of `color`, in linear space or not.
pub(crate) fn color(color: Color32, linear: bool) -> [f32; 4] {
    if linear {
        egui::Rgba::from(color).to_array()
    } else {
        color.to_normalized_gamma_f32()
    }
}

/// Paint the labels of the ticks of the grid next to the axes, x below and y on the left, or along the edge of the plot
/// when an axis is out of view.
fn paint_ticks(ui: &egui::Ui, transform: &PlotTransform) {
    let frame = *transform.frame();
    let painter = ui.painter_at(frame);
    let font = egui::TextStyle::Body.resolve(ui.style());
    let bounds = transform.bounds();
    let origin = transform.position_from_point(&PlotPoint::new(0., 0.));
    for (axis, (hidden, opaque)) in TICK_SPACING.into_iter().enumerate() {
        let marks = egui_plot::log_grid_spacer(10)(GridInput {
            bounds: (bounds.min()[axis], bounds.max()[axis]),
            base_step_size: transform.dvalue_dpos()[axis].abs() * f64::from(hidden),
        });
        let scale = transform.dpos_dvalue()[axis].abs();
        for mark in marks {
            // The origin is labeled once, by y
            let zero = mark.value.abs() < mark.step_size / 2.;
            if zero && axis == 0 {
                continue;
            }
            let spacing = (scale * mark.step_size) as f32;
            if spacing <= hidden {
                continue;
            }
            let strength = egui::emath::remap_clamp(spacing, hidden..=opaque, 0.0..=1.);
            let color = egui_plot::color_from_strength(ui, strength);
            let decimals = (-mark.step_size.log10().round()).max(0.) as usize;
            let text = egui::emath::format_with_decimals_in_range(mark.value, decimals..=decimals);
            let galley = painter.layout_no_wrap(text, font.clone(), color);
            let size = galley.size();
            if spacing < size[axis] + TICK_GAP {
                continue;
            }
            // Below the x axis and left of the y axis
            let below = (origin.y + TICK_GAP)
                .clamp(frame.top() + TICK_GAP, frame.bottom() - size.y - TICK_GAP);
            let left = (origin.x - TICK_GAP - size.x)
                .clamp(frame.left() + TICK_GAP, frame.right() - size.x - TICK_GAP);
            let position = if axis == 0 {
                egui::pos2(
                    transform.position_from_point_x(mark.value) - size.x / 2.,
                    below,
                )
            } else if zero {
                egui::pos2(left, below)
            } else {
                egui::pos2(
                    left,
                    transform.position_from_point_y(mark.value) - size.y / 2.,
                )
            };
            painter.galley(position, galley, color);
        }
    }
}

/// The label of a point of a graph.
/// The points `(k, u_k)` of a sequence for the integers `k` from `x_min` to `x_max`, at most [`MAX_SEQUENCE_POINTS`]
/// of them, evenly spaced, with the values `params` of its parameters.
#[allow(clippy::cast_possible_truncation, clippy::cast_precision_loss)]
fn sequence_points(
    terms: &NumericSequence,
    params: &[f64],
    x_min: f64,
    x_max: f64,
) -> Vec<[f64; 2]> {
    // Beyond, the terms aren't computed anyway
    let bound = |x: f64| x.clamp(-1e15, 1e15) as i64;
    let (from, to) = (bound(x_min.ceil()), bound(x_max.floor()));
    let count = to.saturating_sub(from).saturating_add(1);
    let step = ((count + MAX_SEQUENCE_POINTS - 1) / MAX_SEQUENCE_POINTS).max(1);
    terms
        .terms(params, from, to)
        .into_iter()
        .filter(|(k, _)| (k - from) % step == 0)
        .map(|(k, value)| [k as f64, value])
        .collect()
}

fn label(name: &str, x: f64, y: f64) -> String {
    format!("{name}\n({}, {})", format_number(x), format_number(y))
}

/// Format a coordinate with at most 6 decimals.
pub(crate) fn format_number(value: f64) -> String {
    let rounded = format!("{value:.6}");
    let trimmed = rounded.trim_end_matches('0').trim_end_matches('.');
    if trimmed == "-0" {
        "0".to_owned()
    } else {
        trimmed.to_owned()
    }
}

/// The graph closest to `pointer`, if any is close enough, with the point of the graph there.
fn hover(
    drawables: &[Drawable<'_>],
    pointer: PlotPoint,
    transform: &PlotTransform,
) -> Option<(String, [f64; 2])> {
    profile_scope!("hover");
    // Points per unit
    let kx = transform.dpos_dvalue_x().abs();
    let ky = transform.dpos_dvalue_y().abs();
    let (px, py) = (pointer.x, pointer.y);
    let mut best: Option<(f64, &str, [f64; 2])> = None;
    for drawable in drawables {
        let values = values(&drawable.params);
        let eval = |expr: &Numeric, x: f64, y: f64| {
            let mut values = values.clone();
            values[Graph::X] = x;
            values[Graph::Y] = y;
            expr.eval(&values)
        };
        // The distance to the curve `y = f(x)` and the point of the curve at the pointer
        let curve_hit = |expr: &Numeric, derivative: Option<&Numeric>| {
            let y = eval(expr, px, f64::NAN);
            let slope = derivative.map_or_else(
                || {
                    (eval(expr, px + 1. / kx, f64::NAN) - eval(expr, px - 1. / kx, f64::NAN)) * kx
                        / 2.
                },
                |derivative| eval(derivative, px, f64::NAN),
            );
            let distance = (y - py).abs() * ky / (slope * ky / kx).hypot(1.);
            (distance, [px, y])
        };
        let hit = match &drawable.graph.kind {
            GraphKind::Function { expr, derivative }
            | GraphKind::Integral {
                expr, derivative, ..
            } => curve_hit(expr, derivative.as_ref()),
            GraphKind::ComplexCurve {
                re,
                im,
                re_derivative,
                im_derivative,
            } if drawable.complex_view == ComplexView::Parts => {
                let (re, im) = (
                    curve_hit(re, re_derivative.as_ref()),
                    curve_hit(im, im_derivative.as_ref()),
                );
                // NaN distances lose
                if im.0 < re.0 || re.0.is_nan() { im } else { re }
            }
            GraphKind::InverseFunction { expr } => {
                let x = eval(expr, f64::NAN, py);
                let slope =
                    (eval(expr, f64::NAN, py + 1. / ky) - eval(expr, f64::NAN, py - 1. / ky)) * ky
                        / 2.;
                let distance = (x - px).abs() * kx / (slope * kx / ky).hypot(1.);
                (distance, [x, py])
            }
            GraphKind::Implicit { relations } => {
                // The closest boundary, where the other relations hold
                let hits = relations.iter().enumerate().filter_map(|(i, relation)| {
                    let expr = &relation.expr;
                    let value = eval(expr, px, py);
                    let dx =
                        (eval(expr, px + 1. / kx, py) - eval(expr, px - 1. / kx, py)) * kx / 2.;
                    let dy =
                        (eval(expr, px, py + 1. / ky) - eval(expr, px, py - 1. / ky)) * ky / 2.;
                    let distance = value.abs() / (dx / kx).hypot(dy / ky);
                    // A Newton step towards `F = 0`
                    let norm = dx.mul_add(dx, dy * dy);
                    let point = [px - value * dx / norm, py - value * dy / norm];
                    let others_hold = relations.iter().enumerate().all(|(j, other)| {
                        j == i || other.relation.holds(eval(&other.expr, point[0], point[1]))
                    });
                    others_hold.then_some((distance, point))
                });
                match hits.min_by(|(a, _), (b, _)| a.total_cmp(b)) {
                    Some(hit) => hit,
                    None => continue,
                }
            }
            GraphKind::Sequence { terms } => {
                // The terms whose indices are within the hover distance of the pointer
                let reach = (HOVER_DISTANCE / kx).ceil();
                let points = sequence_points(terms, &drawable.params, px - reach, px + reach);
                match points
                    .into_iter()
                    .map(|[x, y]| (((x - px) * kx).hypot((y - py) * ky), [x, y]))
                    .min_by(|(a, _), (b, _)| a.total_cmp(b))
                {
                    Some(hit) => hit,
                    None => continue,
                }
            }
            GraphKind::Point { .. }
            | GraphKind::Surface { .. }
            | GraphKind::ComplexMap { .. }
            | GraphKind::ComplexCurve { .. } => {
                continue;
            }
        };
        let (distance, point) = hit;
        if distance < HOVER_DISTANCE
            && point.iter().all(|value| value.is_finite())
            && best.is_none_or(|(closest, ..)| distance < closest)
        {
            best = Some((distance, &drawable.name, point));
        }
    }
    best.map(|(_, name, point)| (name.to_owned(), point))
}

/// Implicit relations or a region drawn by its shader.
struct GpuGraph {
    base: PlotItemBase,
    id: u64,
    frame: u64,
    shader: Arc<Shader>,
    color: [f32; 4],
    fill: [f32; 4],
    params: Vec<f32>,
    drawable_color: Color32,
}

impl GpuGraph {
    /// The uniforms of the shader in the view of `transform`.
    #[allow(clippy::cast_possible_truncation)]
    fn uniforms(&self, transform: &PlotTransform, pixels_per_point: f32) -> Box<[f32; UNIFORMS]> {
        let bounds = transform.bounds();
        let frame = transform.frame();
        uniforms(
            &View {
                x_min: bounds.min()[0],
                x_max: bounds.max()[0],
                y_min: bounds.min()[1],
                y_max: bounds.max()[1],
            },
            [frame.width(), frame.height()],
            pixels_per_point,
            self,
        )
    }
}

/// The uniforms of the shader of `graph` drawn in `view` on `size` points, see [`crate::shader::RENDER`].
#[allow(clippy::cast_possible_truncation)]
fn uniforms(
    view: &View,
    size: [f32; 2],
    pixels_per_point: f32,
    graph: &GpuGraph,
) -> Box<[f32; UNIFORMS]> {
    let mut uniforms = Box::new([0.; UNIFORMS]);
    uniforms[..20].copy_from_slice(&[
        view.x_min as f32,
        view.x_max as f32,
        view.y_min as f32,
        view.y_max as f32,
        size[0] * pixels_per_point,
        size[1] * pixels_per_point,
        LINE_WIDTH / 2. * pixels_per_point,
        0.,
        graph.color[0],
        graph.color[1],
        graph.color[2],
        graph.color[3],
        graph.fill[0],
        graph.fill[1],
        graph.fill[2],
        graph.fill[3],
        0.,
        0.,
        DASH_PERIOD * pixels_per_point,
        0.,
    ]);
    uniforms[20..20 + graph.params.len()].copy_from_slice(&graph.params);
    uniforms
}

impl PlotItem for GpuGraph {
    fn shapes(&self, ui: &egui::Ui, transform: &PlotTransform, shapes: &mut Vec<egui::Shape>) {
        let callback = GraphCallback {
            id: self.id,
            frame: self.frame,
            shader: self.shader.clone(),
            uniforms: self.uniforms(transform, ui.ctx().pixels_per_point()),
            #[cfg(feature = "profile")]
            label: self.name().to_owned(),
        };
        shapes.push(egui::Shape::Callback(
            egui_wgpu::Callback::new_paint_callback(*transform.frame(), callback),
        ));
    }

    fn initialize(&mut self, _x_range: RangeInclusive<f64>) {}

    fn color(&self) -> Color32 {
        self.drawable_color
    }

    fn allow_hover(&self) -> bool {
        false
    }

    fn geometry(&self) -> PlotGeometry<'_> {
        PlotGeometry::None
    }

    fn bounds(&self) -> PlotBounds {
        PlotBounds::NOTHING
    }

    fn base(&self) -> &PlotItemBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut PlotItemBase {
        &mut self.base
    }
}

#[cfg(test)]
mod tests {
    use eframe::egui_wgpu::{CallbackTrait as _, wgpu};

    use super::*;
    use crate::{
        gpu::{Resources, tests::device},
        shader::tests::compile,
    };

    const WIDTH: u32 = 384;
    const HEIGHT: u32 = 256;

    const VIEW: View = View {
        x_min: -10.,
        x_max: 10.,
        y_min: -6.,
        y_max: 6.,
    };

    /// The opacity of the pixels of a graph drawn in white in [`VIEW`].
    struct Image(Vec<u8>);

    impl Image {
        /// The opacity at the point `(x, y)`.
        fn at(&self, x: f64, y: f64) -> f32 {
            let column = ((x - VIEW.x_min) / VIEW.width() * f64::from(WIDTH)) as usize;
            let row = ((VIEW.y_max - y) / VIEW.height() * f64::from(HEIGHT)) as usize;
            f32::from(self.0[(row * WIDTH as usize + column) * 4 + 3]) / 255.
        }
    }

    /// Draw the graph of the relations `inputs`, offscreen.
    fn draw(
        device: &(wgpu::Adapter, wgpu::Device, wgpu::Queue),
        inputs: &[(&str, Comparison)],
    ) -> Image {
        let compiled: Vec<(Numeric, Comparison)> = inputs
            .iter()
            .map(|(input, relation)| (compile(input), *relation))
            .collect();
        let relations: Vec<(&Numeric, Comparison)> = compiled
            .iter()
            .map(|(expr, relation)| (expr, *relation))
            .collect();
        draw_shader(device, shader::render(&relations))
    }

    /// Draw a graph with the shader `source`, offscreen, in white (the fill at a quarter of its opacity).
    fn draw_shader(
        (_, device, queue): &(wgpu::Adapter, wgpu::Device, wgpu::Queue),
        source: String,
    ) -> Image {
        let format = wgpu::TextureFormat::Rgba8Unorm;
        let graph = GpuGraph {
            base: PlotItemBase::new(String::new()),
            id: 0,
            frame: 1,
            shader: Shader::new(source),
            color: color(Color32::WHITE, false),
            fill: color(Color32::WHITE.gamma_multiply(0.25), false),
            params: vec![2., -3.],
            drawable_color: Color32::WHITE,
        };
        let callback = GraphCallback {
            id: 0,
            frame: 1,
            shader: graph.shader.clone(),
            uniforms: uniforms(&VIEW, [WIDTH as f32, HEIGHT as f32], 1., &graph),
            #[cfg(feature = "profile")]
            label: String::new(),
        };
        let mut resources = egui_wgpu::CallbackResources::default();
        resources.insert(Resources::new(device, format));
        let texture = device.create_texture(&wgpu::TextureDescriptor {
            label: None,
            size: wgpu::Extent3d {
                width: WIDTH,
                height: HEIGHT,
                depth_or_array_layers: 1,
            },
            mip_level_count: 1,
            sample_count: 1,
            dimension: wgpu::TextureDimension::D2,
            format,
            usage: wgpu::TextureUsages::RENDER_ATTACHMENT | wgpu::TextureUsages::COPY_SRC,
            view_formats: &[],
        });
        let view = texture.create_view(&wgpu::TextureViewDescriptor::default());
        let mut encoder = device.create_command_encoder(&wgpu::CommandEncoderDescriptor::default());
        let screen = egui_wgpu::ScreenDescriptor {
            size_in_pixels: [WIDTH, HEIGHT],
            pixels_per_point: 1.,
        };
        callback.prepare(device, queue, &screen, &mut encoder, &mut resources);
        {
            let pass = encoder.begin_render_pass(&wgpu::RenderPassDescriptor {
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
            let rect = egui::Rect::from_min_size(
                egui::Pos2::ZERO,
                egui::vec2(WIDTH as f32, HEIGHT as f32),
            );
            let info = egui::PaintCallbackInfo {
                viewport: rect,
                clip_rect: rect,
                pixels_per_point: 1.,
                screen_size_px: [WIDTH, HEIGHT],
            };
            callback.paint(info, &mut pass.forget_lifetime(), &resources);
        }
        let size = u64::from(WIDTH * HEIGHT * 4);
        let staging = device.create_buffer(&wgpu::BufferDescriptor {
            label: None,
            size,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        encoder.copy_texture_to_buffer(
            texture.as_image_copy(),
            wgpu::TexelCopyBufferInfo {
                buffer: &staging,
                layout: wgpu::TexelCopyBufferLayout {
                    offset: 0,
                    bytes_per_row: Some(WIDTH * 4),
                    rows_per_image: None,
                },
            },
            texture.size(),
        );
        queue.submit([encoder.finish()]);
        staging.map_async(wgpu::MapMode::Read, .., |result| result.expect("Mapped"));
        let _ = device.poll(wgpu::PollType::wait_indefinitely());
        let data = staging.get_mapped_range(..).expect("Mapped").to_vec();
        Image(data)
    }

    #[test]
    fn test_render() {
        let Some(device) = device() else {
            eprintln!("No GPU, skipped");
            return;
        };
        let implicit = |input, relation| draw(&device, &[(input, relation)]);
        let image = implicit("x^2 + y^2 - 4", Comparison::Equal);
        assert!(image.at(2., 0.) > 0.5 && image.at(0., -2.) > 0.5);
        assert!(image.at(0., 0.) == 0. && image.at(5., 0.) == 0.);
        let image = implicit("x^2 + y^2 - 4", Comparison::Less);
        assert!((image.at(0., 0.) - 0.25).abs() < 0.02);
        assert!(image.at(5., 0.) == 0.);
        let image = implicit("y - sin(x)", Comparison::GreaterEqual);
        assert!((image.at(0., 3.) - 0.25).abs() < 0.02 && image.at(0., -3.) == 0.);
        assert!(image.at(std::f64::consts::FRAC_PI_2, 1.) > 0.5);
        let image = implicit("x^2/25 + y^2/9 - 1", Comparison::Greater);
        assert!(image.at(0., 0.) == 0. && (image.at(9., 5.) - 0.25).abs() < 0.02);
        // No contour at the poles of `y - tan(3 x)`
        let image = implicit("y - tan(3*x)", Comparison::Equal);
        assert!(image.at(0., 0.) > 0.5);
        assert!(image.at(std::f64::consts::FRAC_PI_6, 3.) == 0.);
        // Intersections: the upper half disk, bounded by the arc and the segment, then only the arc
        let half_disk = [
            ("x^2 + y^2 - 4", Comparison::Less),
            ("y", Comparison::GreaterEqual),
        ];
        let image = draw(&device, &half_disk);
        assert!((image.at(0., 1.) - 0.25).abs() < 0.02);
        assert!(image.at(0., -1.) == 0. && image.at(0., 3.) == 0.);
        assert!(image.at(1., 0.) > 0.5);
        assert!(image.at(3., 0.) == 0. && image.at(0., -2.) == 0.);
        let image = draw(
            &device,
            &[
                ("x^2 + y^2 - 4", Comparison::Equal),
                ("y", Comparison::Greater),
            ],
        );
        assert!(image.at(0., 2.) > 0.5);
        assert!(image.at(0., -2.) == 0. && image.at(0., 1.) == 0. && image.at(1., 0.) == 0.);
    }
}
