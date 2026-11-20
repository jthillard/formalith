//! Drawing of the graphs of the lines in an interactive plot, with cached geometry.

use std::{cell::RefCell, collections::HashMap};

use eframe::egui::{self, Color32, ColorImage, TextureHandle, TextureOptions, Vec2b};
use egui_plot::{
    HoverPosition, Line, LineStyle, MarkerShape, Plot, PlotBounds, PlotImage, PlotPoint, Points,
};
use formalith_session::graph::{Comparison, Graph, GraphKind};

use crate::{
    analysis::{self, Kind},
    geometry::{Grid, Polyline, View, sample_function},
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
}

/// The view shown first and after a reset.
const DEFAULT_VIEW: View = View {
    x_min: -10.,
    x_max: 10.,
    y_min: -6.,
    y_max: 6.,
};

/// What is drawn for a graph in a view.
enum Geometry {
    Curves(Vec<Polyline>),
    Region {
        boundary: Vec<Polyline>,
        texture: TextureHandle,
        strict: bool,
    },
    Point([f64; 2]),
}

/// The parameters geometry is computed with: it is computed again when they change.
#[derive(PartialEq)]
struct Key {
    revision: u64,
    view: [u64; 4],
    pixels: [usize; 2],
    params: Vec<u64>,
}

impl Key {
    fn new(drawable: &Drawable<'_>, view: &View, pixels: [usize; 2]) -> Self {
        Self {
            revision: drawable.revision,
            view: [view.x_min, view.x_max, view.y_min, view.y_max].map(f64::to_bits),
            pixels,
            params: drawable
                .params
                .iter()
                .map(|value| value.to_bits())
                .collect(),
        }
    }
}

/// The interactive plot.
#[derive(Default)]
pub struct Plotter {
    cache: HashMap<u64, (Key, Geometry)>,
    remarkable: Option<(Key, Vec<u64>, Vec<analysis::Point>)>,
    reset: bool,
}

/// The values `[x, y, params...]` of an evaluation.
fn values(params: &[f64]) -> RefCell<Vec<f64>> {
    RefCell::new(
        [f64::NAN, f64::NAN]
            .into_iter()
            .chain(params.iter().copied())
            .collect(),
    )
}

/// The function `x -> f(x)` of a [`GraphKind::Function`].
fn function<'a>(
    expr: &'a formalith_session::formalith::field::real::numeric::Numeric,
    params: &[f64],
) -> impl Fn(f64) -> f64 + 'a {
    let values = values(params);
    move |x| {
        let mut values = values.borrow_mut();
        values[Graph::X] = x;
        expr.eval(&values)
    }
}

impl Plotter {
    /// Go back to the default view.
    pub const fn reset_view(&mut self) {
        self.reset = true;
    }

    /// Forget the geometry of the lines which aren't in `ids`.
    pub fn retain(&mut self, ids: &[u64]) {
        self.cache.retain(|id, _| ids.contains(id));
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
        let ctx = ui.ctx().clone();
        let mut plot = Plot::new("plot")
            .default_x_bounds(DEFAULT_VIEW.x_min, DEFAULT_VIEW.x_max)
            .default_y_bounds(DEFAULT_VIEW.y_min, DEFAULT_VIEW.y_max)
            .auto_bounds(Vec2b::FALSE)
            .allow_double_click_reset(false)
            .label_formatter(|position| match position {
                HoverPosition::NearDataPoint {
                    plot_name,
                    position,
                    ..
                } => Some(format!(
                    "{plot_name}\n({}, {})",
                    format_number(position.x),
                    format_number(position.y)
                )),
                HoverPosition::Elsewhere { .. } => None,
            });
        if equal_aspect {
            plot = plot.data_aspect(1.);
        }
        let reset = std::mem::take(&mut self.reset);
        plot.show(ui, |plot_ui| {
            if reset {
                plot_ui.set_plot_bounds(PlotBounds::from_min_max(
                    [DEFAULT_VIEW.x_min, DEFAULT_VIEW.y_min],
                    [DEFAULT_VIEW.x_max, DEFAULT_VIEW.y_max],
                ));
            }
            let bounds = plot_ui.plot_bounds();
            let view = View {
                x_min: bounds.min()[0],
                x_max: bounds.max()[0],
                y_min: bounds.min()[1],
                y_max: bounds.max()[1],
            };
            if !(view.width() > 0. && view.height() > 0.) {
                return;
            }
            let frame = plot_ui.transform().frame();
            let pixels = [frame.width() as usize, frame.height() as usize];
            for drawable in drawables {
                let key = Key::new(drawable, &view, pixels);
                if self
                    .cache
                    .get(&drawable.id)
                    .is_none_or(|(cached, _)| *cached != key)
                {
                    let geometry = compute(&ctx, drawable, &view, pixels);
                    self.cache.insert(drawable.id, (key, geometry));
                }
                let (_, geometry) = &self.cache[&drawable.id];
                draw(plot_ui, drawable, geometry);
            }
            self.draw_remarkable(plot_ui, drawables, selected, &view, pixels);
        });
    }

    /// Draw the remarkable points of the curve `selected`.
    fn draw_remarkable(
        &mut self,
        plot_ui: &mut egui_plot::PlotUi<'_>,
        drawables: &[Drawable<'_>],
        selected: Option<u64>,
        view: &View,
        pixels: [usize; 2],
    ) {
        let Some(drawable) = drawables
            .iter()
            .find(|drawable| Some(drawable.id) == selected)
        else {
            return;
        };
        let GraphKind::Function { expr, derivative } = &drawable.graph.kind else {
            return;
        };
        let others: Vec<&Drawable<'_>> = drawables
            .iter()
            .filter(|other| {
                other.id != drawable.id && matches!(other.graph.kind, GraphKind::Function { .. })
            })
            .collect();
        let key = Key::new(drawable, view, pixels);
        // The points change with the other curves too
        let mut other_keys: Vec<u64> = vec![];
        for other in &others {
            other_keys.push(other.id);
            other_keys.push(other.revision);
            other_keys.extend(other.params.iter().map(|value| value.to_bits()));
        }
        if self
            .remarkable
            .as_ref()
            .is_none_or(|(cached, cached_others, _)| *cached != key || *cached_others != other_keys)
        {
            let samples = (pixels[0] / 2).clamp(50, 1000);
            let f = function(expr, &drawable.params);
            let derivative = derivative
                .as_ref()
                .map(|derivative| function(derivative, &drawable.params));
            let derivative = derivative
                .as_ref()
                .map(|derivative| derivative as &dyn Fn(f64) -> f64);
            let mut points =
                analysis::remarkable_points(&f, derivative, view.x_min, view.x_max, samples);
            for other in others {
                if let GraphKind::Function { expr, .. } = &other.graph.kind {
                    let g = function(expr, &other.params);
                    points.extend(analysis::intersections(
                        &f, &g, view.x_min, view.x_max, samples,
                    ));
                }
            }
            points.retain(|point| point.y.is_finite());
            self.remarkable = Some((key, other_keys, points));
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

/// Format a coordinate with at most 6 decimals.
fn format_number(value: f64) -> String {
    let rounded = format!("{value:.6}");
    let trimmed = rounded.trim_end_matches('0').trim_end_matches('.');
    if trimmed == "-0" {
        "0".to_owned()
    } else {
        trimmed.to_owned()
    }
}

/// Compute what to draw for `drawable` in `view`.
fn compute(
    ctx: &egui::Context,
    drawable: &Drawable<'_>,
    view: &View,
    pixels: [usize; 2],
) -> Geometry {
    let values = values(&drawable.params);
    match &drawable.graph.kind {
        GraphKind::Function { expr, .. } => Geometry::Curves(sample_function(
            function(expr, &drawable.params),
            view,
            pixels[0],
        )),
        GraphKind::InverseFunction { expr } => {
            let g = |y: f64| {
                let mut values = values.borrow_mut();
                values[Graph::Y] = y;
                expr.eval(&values)
            };
            let curves = sample_function(g, &view.transposed(), pixels[1]);
            Geometry::Curves(
                curves
                    .into_iter()
                    .map(|curve| curve.into_iter().map(|[y, x]| [x, y]).collect())
                    .collect(),
            )
        }
        GraphKind::Implicit { expr, relation } => {
            let f = |x: f64, y: f64| {
                let mut values = values.borrow_mut();
                values[Graph::X] = x;
                values[Graph::Y] = y;
                expr.eval(&values)
            };
            // About 3 pixels per cell
            let nx = (pixels[0] / 3).clamp(20, 400);
            let ny = (pixels[1] / 3).clamp(20, 400);
            let grid = Grid::new(f, view, nx, ny);
            let boundary = grid.contour(f);
            if *relation == Comparison::Equal {
                return Geometry::Curves(boundary);
            }
            let mask = grid.mask(f, |value| relation.holds(value));
            let fill = drawable.color.gamma_multiply(0.25);
            let pixels: Vec<Color32> = mask
                .into_iter()
                .map(|inside| if inside { fill } else { Color32::TRANSPARENT })
                .collect();
            let image = ColorImage {
                size: [grid.nx, grid.ny],
                source_size: egui::vec2(grid.nx as f32, grid.ny as f32),
                pixels,
            };
            let texture = ctx.load_texture(
                format!("region-{}", drawable.id),
                image,
                TextureOptions::LINEAR,
            );
            Geometry::Region {
                boundary,
                texture,
                strict: relation.is_strict(),
            }
        }
        GraphKind::Point { x, y } => {
            let values = values.borrow();
            Geometry::Point([x.eval(&values), y.eval(&values)])
        }
    }
}

/// Draw the geometry of `drawable`.
fn draw(plot_ui: &mut egui_plot::PlotUi<'_>, drawable: &Drawable<'_>, geometry: &Geometry) {
    let curves = |plot_ui: &mut egui_plot::PlotUi<'_>, curves: &[Polyline], style: LineStyle| {
        for (k, curve) in curves.iter().enumerate() {
            plot_ui.line(
                Line::new(drawable.name.clone(), curve.clone())
                    .id((drawable.id, k))
                    .color(drawable.color)
                    .width(2.5)
                    .style(style),
            );
        }
    };
    match geometry {
        Geometry::Curves(lines) => curves(plot_ui, lines, LineStyle::Solid),
        Geometry::Region {
            boundary,
            texture,
            strict,
        } => {
            let bounds = plot_ui.plot_bounds();
            let center = bounds.center();
            let size = egui::vec2(bounds.width() as f32, bounds.height() as f32);
            plot_ui.image(
                PlotImage::new(
                    drawable.name.clone(),
                    texture.id(),
                    PlotPoint::new(center.x, center.y),
                    size,
                )
                .allow_hover(false),
            );
            let style = if *strict {
                LineStyle::dashed_loose()
            } else {
                LineStyle::Solid
            };
            curves(plot_ui, boundary, style);
        }
        Geometry::Point([x, y]) => {
            if x.is_finite() && y.is_finite() {
                plot_ui.points(
                    Points::new(drawable.name.clone(), vec![[*x, *y]])
                        .id(drawable.id)
                        .shape(MarkerShape::Circle)
                        .radius(5.)
                        .filled(true)
                        .color(drawable.color),
                );
            }
        }
    }
}
