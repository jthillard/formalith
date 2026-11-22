//! Drawing of the graphs of the lines in an interactive plot, on the GPU: each graph is a plot item running its
//! shader over the plot ([`crate::gpu`]), and the remarkable points of the selected curve are searched in compute
//! shaders when the GPU has them ([`crate::gpu::analysis`]).

use std::{collections::HashMap, ops::RangeInclusive, sync::Arc};

use eframe::{
    egui::{self, Color32, Vec2b},
    egui_wgpu,
};
use egui_plot::{
    HoverPosition, MarkerShape, Plot, PlotBounds, PlotGeometry, PlotItem, PlotItemBase, PlotPoint,
    PlotTransform, Points,
};
use formalith_session::{
    formalith::field::real::numeric::Numeric,
    graph::{Comparison, Graph, GraphKind},
};

use crate::{
    geometry::View,
    gpu::{
        self, GraphCallback, Shader, UNIFORMS,
        analysis::{Analyzer, Kind, Point, Request},
    },
    shader::{self, AnalysisCurves, MAX_PARAMS},
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

/// The width of lines, in points.
const LINE_WIDTH: f32 = 2.5;

/// The period of dashes of strict boundaries, in points.
const DASH_PERIOD: f32 = 10.;

/// Distance in points from a graph under which it is hovered.
const HOVER_DISTANCE: f64 = 6.;

/// What the remarkable points of the selected curve depend on, besides the view: its line, revision and
/// parameters, and those of the other curves.
type Content = Vec<u64>;

/// The range and number of samples of a search of remarkable points.
type Range = [u64; 3];

/// The interactive plot.
#[derive(Default)]
pub struct Plotter {
    /// Whether the GPU is set up, and colors are given in linear space.
    gpu: Option<bool>,
    /// The shader of each line, with the revision it was made for.
    shaders: HashMap<u64, (u64, Arc<Shader>)>,
    analyzer: Option<Analyzer>,
    /// The last points found.
    remarkable: Option<(Content, Range, Vec<Point>)>,
    /// The running search.
    searching: Option<(Content, Range)>,
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

impl Plotter {
    /// The plot, drawing with the GPU of `cc`.
    #[must_use]
    pub fn new(cc: &eframe::CreationContext<'_>) -> Self {
        let Some(render_state) = &cc.wgpu_render_state else {
            return Self::default();
        };
        let ctx = cc.egui_ctx.clone();
        Self {
            gpu: Some(gpu::install(render_state)),
            analyzer: Analyzer::new(
                &render_state.adapter,
                render_state.device.clone(),
                render_state.queue.clone(),
                Arc::new(move || ctx.request_repaint()),
            ),
            ..Self::default()
        }
    }

    /// Go back to the default view.
    pub const fn reset_view(&mut self) {
        self.reset = true;
    }

    /// Forget the shaders of the lines which aren't in `ids`.
    pub fn retain(&mut self, ids: &[u64]) {
        self.shaders.retain(|id, _| ids.contains(id));
    }

    /// The shader of `drawable`.
    fn shader(
        &mut self,
        drawable: &Drawable<'_>,
        relations: &[(&Numeric, Comparison)],
    ) -> Arc<Shader> {
        profile_scope!("Plotter::shader");
        match self.shaders.get(&drawable.id) {
            Some((revision, shader)) if *revision == drawable.revision => shader.clone(),
            _ => {
                let shader = Shader::new(shader::render(relations));
                self.shaders
                    .insert(drawable.id, (drawable.revision, shader.clone()));
                shader
            }
        }
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
            for drawable in drawables {
                self.draw(plot_ui, drawable);
            }
            let pixels =
                (plot_ui.transform().frame().width() * plot_ui.ctx().pixels_per_point()) as usize;
            self.draw_remarkable(plot_ui, drawables, selected, &bounds, pixels);
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
        if let Some((name, [x, y])) = response.inner {
            response
                .response
                .on_hover_text_at_pointer(label(&name, x, y));
        }
    }

    /// Draw `drawable`.
    fn draw(&mut self, plot_ui: &mut egui_plot::PlotUi<'_>, drawable: &Drawable<'_>) {
        profile_scope!("Plotter::draw", &drawable.name);
        let (kind, relations) = match &drawable.graph.kind {
            GraphKind::Function { expr, .. } => (0., vec![(expr, Comparison::Equal)]),
            GraphKind::InverseFunction { expr } => (1., vec![(expr, Comparison::Equal)]),
            GraphKind::Implicit { relations } => (
                2.,
                relations
                    .iter()
                    .map(|relation| (&relation.expr, relation.relation))
                    .collect(),
            ),
            GraphKind::Point { x, y } => {
                let values = values(&drawable.params);
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
                return;
            }
        };
        let Some(linear) = self.gpu else {
            return;
        };
        if drawable.params.len() > MAX_PARAMS {
            return;
        }
        let shader = self.shader(drawable, &relations);
        #[allow(clippy::cast_possible_truncation)]
        let params = drawable.params.iter().map(|value| *value as f32).collect();
        plot_ui.add(GpuGraph {
            base: PlotItemBase::new(drawable.name.clone()),
            id: drawable.id,
            frame: self.frame,
            shader,
            color: color(drawable.color, linear),
            fill: color(drawable.color.gamma_multiply(0.25), linear),
            kind,
            params,
            drawable_color: drawable.color,
        });
    }

    /// Draw the remarkable points of the curve `selected`, searching them again when it or the view changed.
    fn draw_remarkable(
        &mut self,
        plot_ui: &mut egui_plot::PlotUi<'_>,
        drawables: &[Drawable<'_>],
        selected: Option<u64>,
        bounds: &PlotBounds,
        pixels: usize,
    ) {
        profile_scope!("Plotter::draw_remarkable");
        let Some(analyzer) = &mut self.analyzer else {
            return;
        };
        if let Some(points) = analyzer.poll() {
            if let Some((content, range)) = self.searching.take() {
                self.remarkable = Some((content, range, points));
            }
        }
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
        let mut content: Content = vec![];
        for curve in std::iter::once(drawable).chain(others.iter().copied()) {
            content.push(curve.id);
            content.push(curve.revision);
            content.extend(curve.params.iter().map(|value| value.to_bits()));
        }
        let samples = (pixels / 2).clamp(50, 1000);
        let range = [
            bounds.min()[0].to_bits(),
            bounds.max()[0].to_bits(),
            samples as u64,
        ];
        let current = self
            .remarkable
            .as_ref()
            .is_some_and(|(cached, cached_range, _)| *cached == content && *cached_range == range);
        if !current && !analyzer.is_busy() {
            let curves = AnalysisCurves {
                f: (expr, drawable.params.len()),
                derivative: derivative.as_ref(),
                others: others
                    .iter()
                    .filter_map(|other| match &other.graph.kind {
                        GraphKind::Function { expr, .. } => Some((expr, other.params.len())),
                        _ => None,
                    })
                    .collect(),
            };
            #[allow(clippy::cast_possible_truncation)]
            let params = std::iter::once(drawable)
                .chain(others.iter().copied())
                .flat_map(|curve| curve.params.iter().map(|value| *value as f32))
                .collect();
            let request = Request {
                curves,
                params,
                a: bounds.min()[0],
                b: bounds.max()[0],
                samples,
            };
            if analyzer.start(&request) {
                self.searching = Some((content.clone(), range));
            }
        }
        if analyzer.is_busy() {
            // Natively, the readback progresses when polled
            plot_ui.ctx().request_repaint();
        }
        // Points found in another view are still right
        let Some((_, _, points)) = self
            .remarkable
            .as_ref()
            .filter(|(cached, _, _)| *cached == content)
        else {
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

/// The premultiplied components of `color`, in linear space or not.
fn color(color: Color32, linear: bool) -> [f32; 4] {
    if linear {
        egui::Rgba::from(color).to_array()
    } else {
        color.to_normalized_gamma_f32()
    }
}

/// The label of a point of a graph.
fn label(name: &str, x: f64, y: f64) -> String {
    format!("{name}\n({}, {})", format_number(x), format_number(y))
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
        let hit = match &drawable.graph.kind {
            GraphKind::Function { expr, derivative } => {
                let y = eval(expr, px, f64::NAN);
                let slope = derivative.as_ref().map_or_else(
                    || {
                        (eval(expr, px + 1. / kx, f64::NAN) - eval(expr, px - 1. / kx, f64::NAN))
                            * kx
                            / 2.
                    },
                    |derivative| eval(derivative, px, f64::NAN),
                );
                let distance = (y - py).abs() * ky / (slope * ky / kx).hypot(1.);
                (distance, [px, y])
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
            GraphKind::Point { .. } => continue,
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

/// A graph drawn by its shader.
struct GpuGraph {
    base: PlotItemBase,
    id: u64,
    frame: u64,
    shader: Arc<Shader>,
    color: [f32; 4],
    fill: [f32; 4],
    /// The kind of graph, see [`crate::shader::RENDER`].
    kind: f32,
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
        graph.kind,
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

        /// The largest opacity in the column of `x`.
        fn column(&self, x: f64) -> f32 {
            (0..HEIGHT)
                .map(|row| {
                    let y = VIEW.y_max - (f64::from(row) + 0.5) / f64::from(HEIGHT) * VIEW.height();
                    self.at(x, y)
                })
                .fold(0., f32::max)
        }
    }

    /// Draw the graph of the relations `inputs` of the kind `kind`, offscreen.
    fn draw(
        (_, device, queue): &(wgpu::Adapter, wgpu::Device, wgpu::Queue),
        inputs: &[(&str, Comparison)],
        kind: f32,
    ) -> Image {
        let compiled: Vec<(Numeric, Comparison)> = inputs
            .iter()
            .map(|(input, relation)| (compile(input), *relation))
            .collect();
        let relations: Vec<(&Numeric, Comparison)> = compiled
            .iter()
            .map(|(expr, relation)| (expr, *relation))
            .collect();
        let format = wgpu::TextureFormat::Rgba8Unorm;
        let graph = GpuGraph {
            base: PlotItemBase::new(String::new()),
            id: 0,
            frame: 1,
            shader: Shader::new(shader::render(&relations)),
            color: color(Color32::WHITE, false),
            fill: color(Color32::WHITE.gamma_multiply(0.25), false),
            kind,
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
        let curve = |input| draw(&device, &[(input, Comparison::Equal)], 0.);
        let image = curve("x^2");
        assert!(image.at(1., 1.) > 0.5);
        assert!(image.at(1., 3.) == 0.);
        assert!(image.at(0., -3.) == 0.);
        assert!(image.at(2.4, 2.4_f64.powi(2)) > 0.5);
        // No vertical lines at poles and steps
        let image = curve("1/x");
        assert!(image.at(2., 0.5) > 0.5);
        assert!(image.at(0., 3.) == 0. && image.at(0., -3.) == 0.);
        let image = curve("tan(x)");
        assert!(image.at(0., 0.) > 0.5);
        let pole = std::f64::consts::FRAC_PI_2;
        assert!(image.at(pole, 0.) == 0. && image.at(-pole, 2.) == 0.);
        // Narrow branches still go to the edges near their poles, without vertical lines
        let image = curve("tan(4*x)");
        let pole = std::f64::consts::FRAC_PI_8;
        let pixel = VIEW.width() / f64::from(WIDTH);
        let near = |y| {
            (-3..=3)
                .map(|k| image.at(pole + f64::from(k) * pixel, y))
                .fold(0., f32::max)
        };
        assert!(near(5.5) > 0.5 && near(-5.5) > 0.5);
        assert!(image.at(pole, 0.) == 0.);
        let image = curve("floor(x)");
        assert!(image.at(0.5, 0.) > 0.5);
        assert!(image.at(1., 0.5) == 0.);
        // The domain of `sqrt` starts at 0
        let image = curve("sqrt(x)");
        assert!(image.at(-1., 0.) == 0.);
        assert!(image.column(0.03) > 0.5);
        assert!(image.at(4., 2.) > 0.5);
        // Parameters `a = 2`, `b = -3`
        let image = curve("a*x + b");
        assert!(image.at(3., 3.) > 0.5);
        let image = draw(&device, &[("y^2", Comparison::Equal)], 1.);
        assert!(image.at(1., 1.) > 0.5 && image.at(4., -2.) > 0.5);
        assert!(image.at(1., 3.) == 0.);
        let implicit = |input, relation| draw(&device, &[(input, relation)], 2.);
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
        let image = draw(&device, &half_disk, 2.);
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
            2.,
        );
        assert!(image.at(0., 2.) > 0.5);
        assert!(image.at(0., -2.) == 0. && image.at(0., 1.) == 0. && image.at(1., 0.) == 0.);
    }
}
