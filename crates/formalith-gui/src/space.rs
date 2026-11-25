//! The 3D view: surfaces `z = f(x, y)` ([`GraphKind::Surface`]) and complex functions `f(z)`
//! ([`GraphKind::ComplexMap`], height `|f|`, colored by `arg f`) over a square domain, in a box seen by an orbiting
//! camera. Surfaces are evaluated and drawn on the GPU ([`crate::shader::surface`], [`crate::gpu::scene`]); the
//! height range is chosen from a coarse sample on the CPU, and the box with its ticks is painted by egui on top.
//!
//! Coordinates are normalized to the box `[-1, 1]^3`: `x` and `y` over the domain `center ± radius`, `z` over the
//! height range.

use std::{collections::HashMap, sync::Arc};

use eframe::{
    egui::{self, PointerButton, Pos2, Sense, Stroke},
    egui_wgpu,
};
use formalith_session::graph::{Graph, GraphKind};

use crate::{
    gpu::{
        Shader,
        scene::{RESOLUTION, SURFACE_UNIFORMS, SceneCallback, SurfaceDraw},
    },
    plot::{Drawable, color, format_number},
    shader::{self, MAX_PARAMS, SurfaceKind},
};

/// A 4×4 matrix, by rows.
type Mat4 = [[f64; 4]; 4];

/// The vertical field of view, in radians.
const FOV: f64 = 0.6;

/// The distance of the camera from the center of the box.
const DISTANCE: f64 = 6.;

/// The samples along each side of the domain when choosing the height range.
const RANGE_SAMPLES: usize = 33;

/// The steps along the ray through the pointer when searching the surface under it.
const HIT_STEPS: u32 = 256;

/// Distance in points between a tick label and its edge.
const LABEL_GAP: f32 = 14.;

/// The orbiting camera and the domain it shows.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Camera {
    /// The angle around the `z` axis.
    pub yaw: f64,
    /// The angle above the plane `z = 0`.
    pub pitch: f64,
    /// The center `(x, y)` of the domain.
    pub center: [f64; 2],
    /// Half the side of the domain.
    pub radius: f64,
}

impl Default for Camera {
    fn default() -> Self {
        Self {
            yaw: -2.2,
            pitch: 0.5,
            center: [0., 0.],
            radius: 5.,
        }
    }
}

impl Camera {
    /// The position of the camera in the box.
    fn eye(&self) -> [f64; 3] {
        [
            DISTANCE * self.pitch.cos() * self.yaw.cos(),
            DISTANCE * self.pitch.cos() * self.yaw.sin(),
            DISTANCE * self.pitch.sin(),
        ]
    }

    /// The matrix from the box to clip space, for a view of `aspect` width per height.
    fn view_proj(&self, aspect: f64) -> Mat4 {
        mul(&perspective(FOV, aspect, 0.1, 100.), &look_at(self.eye()))
    }

    /// The direction of the ray from the camera through the point `ndc` of the screen (from `-1` to `1`, `y`
    /// upwards), for a view of `aspect` width per height.
    fn ray(&self, ndc: [f64; 2], aspect: f64) -> [f64; 3] {
        let [side, up, forward] = basis(self.eye());
        let scale = (FOV / 2.).tan();
        let (u, v) = (ndc[0] * scale * aspect, ndc[1] * scale);
        [0, 1, 2].map(|k| forward[k] + side[k] * u + up[k] * v)
    }

    /// The domain `[x_min, x_max, y_min, y_max]`.
    fn domain(&self) -> [f64; 4] {
        let [cx, cy] = self.center;
        let r = self.radius;
        [cx - r, cx + r, cy - r, cy + r]
    }
}

/// The product `a b`.
fn mul(a: &Mat4, b: &Mat4) -> Mat4 {
    let mut out = [[0.; 4]; 4];
    for (i, row) in out.iter_mut().enumerate() {
        for (j, value) in row.iter_mut().enumerate() {
            *value = (0..4).map(|k| a[i][k] * b[k][j]).sum();
        }
    }
    out
}

/// A right-handed perspective projection with the depth from 0 (`near`) to 1 (`far`), as in wgpu.
fn perspective(fov: f64, aspect: f64, near: f64, far: f64) -> Mat4 {
    let f = 1. / (fov / 2.).tan();
    let depth = far / (near - far);
    [
        [f / aspect, 0., 0., 0.],
        [0., f, 0., 0.],
        [0., 0., depth, near * depth],
        [0., 0., -1., 0.],
    ]
}

/// The unit vectors `[side, up, forward]` of a camera at `eye` looking towards the origin, `z` upwards.
fn basis(eye: [f64; 3]) -> [[f64; 3]; 3] {
    let normalize = |v: [f64; 3]| {
        let norm = v.iter().map(|c| c * c).sum::<f64>().sqrt();
        v.map(|c| c / norm)
    };
    let cross = |a: [f64; 3], b: [f64; 3]| {
        [
            a[1] * b[2] - a[2] * b[1],
            a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0],
        ]
    };
    let forward = normalize(eye.map(|c| -c));
    let side = normalize(cross(forward, [0., 0., 1.]));
    [side, cross(side, forward), forward]
}

/// The view from `eye` towards the origin, `z` upwards.
fn look_at(eye: [f64; 3]) -> Mat4 {
    let dot = |a: [f64; 3], b: [f64; 3]| a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
    let [side, up, forward] = basis(eye);
    [
        [side[0], side[1], side[2], -dot(side, eye)],
        [up[0], up[1], up[2], -dot(up, eye)],
        [-forward[0], -forward[1], -forward[2], dot(forward, eye)],
        [0., 0., 0., 1.],
    ]
}

/// The point of the box `p` in clip space.
fn project(m: &Mat4, p: [f64; 3]) -> [f64; 4] {
    let p = [p[0], p[1], p[2], 1.];
    m.map(|row| (0..4).map(|k| row[k] * p[k]).sum())
}

/// The point of the box `p` on the screen in `rect`, `None` behind the camera.
#[allow(clippy::cast_possible_truncation)]
fn to_screen(m: &Mat4, rect: egui::Rect, p: [f64; 3]) -> Option<Pos2> {
    let [x, y, _, w] = project(m, p);
    (w > 1e-6).then(|| {
        let (x, y) = ((x / w) as f32, (y / w) as f32);
        egui::pos2(
            rect.left() + (x + 1.) / 2. * rect.width(),
            rect.top() + (1. - y) / 2. * rect.height(),
        )
    })
}

/// A round step close to `span / 5`: 1, 2 or 5 times a power of 10.
fn nice_step(span: f64) -> f64 {
    let raw = span / 5.;
    let power = 10_f64.powf(raw.log10().floor());
    let ratio = raw / power;
    power
        * if ratio < 1.5 {
            1.
        } else if ratio < 3.5 {
            2.
        } else if ratio < 7.5 {
            5.
        } else {
            10.
        }
}

/// What the height range depends on: the camera's domain, and the lines, revisions and parameters of the surfaces.
type RangeKey = Vec<u64>;

/// The 3D view.
#[derive(Default)]
pub struct Space {
    /// Whether the GPU is set up, and colors are given in linear space.
    gpu: Option<bool>,
    camera: Camera,
    /// The shaders of each line, with the revision they were made for.
    shaders: HashMap<u64, (u64, Arc<Shader>)>,
    /// The last height range.
    range: Option<(RangeKey, [f64; 2])>,
    frame: u64,
}

/// The height of a surface at `(x, y)`, with the values `values` of `[x, y, params...]`.
fn height(graph: &Graph, values: &mut [f64], x: f64, y: f64) -> f64 {
    values[Graph::X] = x;
    values[Graph::Y] = y;
    match &graph.kind {
        GraphKind::Surface { expr } => expr.eval(values),
        GraphKind::ComplexMap { re, im } => re.eval(values).hypot(im.eval(values)),
        _ => f64::NAN,
    }
}

/// Whether the graph is drawn in the 3D view.
#[must_use]
pub const fn is_surface(graph: &Graph) -> bool {
    matches!(
        graph.kind,
        GraphKind::Surface { .. } | GraphKind::ComplexMap { .. }
    )
}

impl Space {
    /// The 3D view, drawing with the GPU if `gpu` is given, and colors in linear space if it is `true`.
    #[must_use]
    pub fn new(gpu: Option<bool>) -> Self {
        Self {
            gpu,
            ..Self::default()
        }
    }

    /// Go back to the default view.
    pub fn reset_view(&mut self) {
        self.camera = Camera::default();
    }

    /// Forget the shaders of the lines which aren't in `ids`.
    pub fn retain(&mut self, ids: &[u64]) {
        self.shaders.retain(|id, _| ids.contains(id));
    }

    /// The shader of the surface `drawable`.
    fn shader(&mut self, drawable: &Drawable<'_>) -> Option<Arc<Shader>> {
        let kind = match &drawable.graph.kind {
            GraphKind::Surface { expr } => SurfaceKind::Real(expr),
            GraphKind::ComplexMap { re, im } => SurfaceKind::Complex { re, im },
            _ => return None,
        };
        Some(match self.shaders.get(&drawable.id) {
            Some((revision, shader)) if *revision == drawable.revision => shader.clone(),
            _ => {
                profile_scope!("Space::shader");
                let shader = Shader::new(shader::surface(kind));
                self.shaders
                    .insert(drawable.id, (drawable.revision, shader.clone()));
                shader
            }
        })
    }

    /// The height range of `surfaces` over the domain: most of their sampled values, padded.
    fn range(&mut self, surfaces: &[&Drawable<'_>]) -> [f64; 2] {
        let domain = self.camera.domain();
        let key: RangeKey = domain
            .iter()
            .map(|value| value.to_bits())
            .chain(surfaces.iter().flat_map(|drawable| {
                [drawable.id, drawable.revision]
                    .into_iter()
                    .chain(drawable.params.iter().map(|value| value.to_bits()))
            }))
            .collect();
        if let Some((cached, range)) = &self.range
            && *cached == key
        {
            return *range;
        }
        profile_scope!("Space::range");
        let mut heights = vec![];
        #[allow(clippy::cast_precision_loss)]
        let last = (RANGE_SAMPLES - 1) as f64;
        for drawable in surfaces {
            let mut values: Vec<f64> = [f64::NAN, f64::NAN]
                .into_iter()
                .chain(drawable.params.iter().copied())
                .collect();
            for i in 0..RANGE_SAMPLES {
                for j in 0..RANGE_SAMPLES {
                    #[allow(clippy::cast_precision_loss)]
                    let (s, t) = (i as f64 / last, j as f64 / last);
                    let x = domain[0] + s * (domain[1] - domain[0]);
                    let y = domain[2] + t * (domain[3] - domain[2]);
                    heights.push(height(drawable.graph, &mut values, x, y));
                }
            }
        }
        let range = height_range(heights, self.camera.radius);
        self.range = Some((key, range));
        range
    }

    /// Show the view of the surfaces among `drawables`, with the camera moved by dragging (rotation, or panning with
    /// the secondary button) and scrolling (zoom).
    pub fn show(&mut self, ui: &mut egui::Ui, drawables: &[Drawable<'_>]) {
        profile_scope!("Space::show");
        self.frame += 1;
        let rect = ui.available_rect_before_wrap();
        let response = ui.allocate_rect(rect, Sense::click_and_drag());
        let surfaces: Vec<&Drawable<'_>> = drawables
            .iter()
            .filter(|drawable| is_surface(drawable.graph) && drawable.params.len() <= MAX_PARAMS)
            .collect();
        let range = (!surfaces.is_empty()).then(|| self.range(&surfaces));
        self.interact(ui, &response, &surfaces, range);
        let painter = ui.painter_at(rect);
        // Again, since the interaction may have moved the domain
        let Some(range) = range.map(|_| self.range(&surfaces)) else {
            painter.text(
                rect.center(),
                egui::Align2::CENTER_CENTER,
                "No surface: draw functions of x and y, like z = x*y,\nor functions of z in C",
                egui::TextStyle::Body.resolve(ui.style()),
                ui.visuals().weak_text_color(),
            );
            return;
        };
        let view_proj = self
            .camera
            .view_proj(f64::from(rect.width() / rect.height()));
        if let Some(linear) = self.gpu {
            let draws = surfaces
                .iter()
                .filter_map(|drawable| {
                    Some(SurfaceDraw {
                        id: drawable.id,
                        shader: self.shader(drawable)?,
                        uniforms: uniforms(&self.camera, &view_proj, range, drawable, linear),
                    })
                })
                .collect();
            let pixels_per_point = ui.ctx().pixels_per_point();
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            let size =
                [rect.width(), rect.height()].map(|side| (side * pixels_per_point).round() as u32);
            painter.add(egui_wgpu::Callback::new_paint_callback(
                rect,
                SceneCallback {
                    frame: self.frame,
                    size,
                    surfaces: draws,
                },
            ));
        }
        self.paint_box(ui, &painter, rect, &view_proj, range);
    }

    /// Move the camera with the pointer over `response`, zooming towards the point of `surfaces` (drawn over the
    /// height range `range`) under the pointer, or the center of the domain.
    fn interact(
        &mut self,
        ui: &egui::Ui,
        response: &egui::Response,
        surfaces: &[&Drawable<'_>],
        range: Option<[f64; 2]>,
    ) {
        let anchor = range
            .zip(response.hover_pos())
            .and_then(|(range, pointer)| self.hit(surfaces, range, response.rect, pointer));
        let camera = &mut self.camera;
        let delta = response.drag_delta();
        if response.dragged_by(PointerButton::Primary) {
            camera.yaw -= f64::from(delta.x) * 0.01;
            camera.pitch = (camera.pitch + f64::from(delta.y) * 0.01).clamp(-1.5, 1.5);
        } else if response.dragged_by(PointerButton::Secondary)
            || response.dragged_by(PointerButton::Middle)
        {
            // In the plane, the content following the pointer
            let scale = 2. * camera.radius / f64::from(response.rect.height().max(1.)) * 2.;
            let (sin, cos) = camera.yaw.sin_cos();
            let right = [-sin, cos];
            let forward = [-cos, -sin];
            for k in 0..2 {
                camera.center[k] +=
                    (-right[k] * f64::from(delta.x) + forward[k] * f64::from(delta.y)) * scale;
            }
        }
        if response.double_clicked() {
            *camera = Camera::default();
        }
        if response.hovered() {
            let speed = ui
                .ctx()
                .options(|options| options.input_options.scroll_zoom_speed);
            let scroll = ui.ctx().input(|input| input.smooth_scroll_delta.y);
            if scroll != 0. {
                let radius = (camera.radius / f64::from((speed * scroll).exp())).clamp(1e-6, 1e9);
                // The point under the pointer stays in place in the domain
                if let Some(anchor) = anchor {
                    let ratio = radius / camera.radius;
                    for k in 0..2 {
                        camera.center[k] = anchor[k] + (camera.center[k] - anchor[k]) * ratio;
                    }
                }
                camera.radius = radius;
            }
        }
    }

    /// The point `(x, y)` of the domain where the ray through `pointer` in `rect` first meets one of `surfaces`,
    /// drawn over the height range `range`, inside the box.
    fn hit(
        &self,
        surfaces: &[&Drawable<'_>],
        range: [f64; 2],
        rect: egui::Rect,
        pointer: Pos2,
    ) -> Option<[f64; 2]> {
        profile_scope!("Space::hit");
        let ndc = [
            f64::from((pointer.x - rect.left()) / rect.width() * 2. - 1.),
            f64::from(1. - (pointer.y - rect.top()) / rect.height() * 2.),
        ];
        let eye = self.camera.eye();
        let dir = self
            .camera
            .ray(ndc, f64::from(rect.width() / rect.height()));
        // The part of the ray inside the box
        let (mut enter, mut exit) = (0_f64, f64::INFINITY);
        for k in 0..3 {
            if dir[k].abs() < 1e-12 {
                if eye[k].abs() > 1. {
                    return None;
                }
                continue;
            }
            let (a, b) = ((-1. - eye[k]) / dir[k], (1. - eye[k]) / dir[k]);
            enter = enter.max(a.min(b));
            exit = exit.min(a.max(b));
        }
        if enter >= exit {
            return None;
        }
        let domain = self.camera.domain();
        let at = |t: f64| [0, 1, 2].map(|k| eye[k] + dir[k] * t);
        let to_domain = |p: [f64; 3]| {
            [
                domain[0] + (p[0] + 1.) / 2. * (domain[1] - domain[0]),
                domain[2] + (p[1] + 1.) / 2. * (domain[3] - domain[2]),
            ]
        };
        // The height of the ray above the surface, in the box
        let above = |drawable: &Drawable<'_>, values: &mut [f64], t: f64| {
            let p = at(t);
            let [x, y] = to_domain(p);
            let z = height(drawable.graph, values, x, y);
            p[2] - (2. * (z - range[0]) / (range[1] - range[0]) - 1.)
        };
        let mut first: Option<f64> = None;
        for drawable in surfaces {
            let mut values: Vec<f64> = [f64::NAN, f64::NAN]
                .into_iter()
                .chain(drawable.params.iter().copied())
                .collect();
            let end = first.unwrap_or(exit);
            let mut previous = (enter, above(drawable, &mut values, enter));
            for step in 1..=HIT_STEPS {
                let t = enter + (end - enter) * f64::from(step) / f64::from(HIT_STEPS);
                let value = above(drawable, &mut values, t);
                if previous.1.is_finite()
                    && value.is_finite()
                    && (previous.1 <= 0.) != (value <= 0.)
                {
                    // Refined by bisection
                    let (mut low, mut high) = (previous.0, t);
                    let sign = previous.1 <= 0.;
                    for _ in 0..40 {
                        let middle = (low + high) / 2.;
                        if (above(drawable, &mut values, middle) <= 0.) == sign {
                            low = middle;
                        } else {
                            high = middle;
                        }
                    }
                    first = Some((low + high) / 2.);
                    break;
                }
                previous = (t, value);
            }
        }
        first.map(|t| to_domain(at(t)))
    }

    /// Paint the edges of the box, with tick labels on an edge along each axis.
    #[allow(clippy::many_single_char_names)]
    fn paint_box(
        &self,
        ui: &egui::Ui,
        painter: &egui::Painter,
        rect: egui::Rect,
        view_proj: &Mat4,
        range: [f64; 2],
    ) {
        let visuals = ui.visuals();
        let stroke = Stroke::new(1., visuals.text_color().gamma_multiply(0.5));
        let font = egui::TextStyle::Body.resolve(ui.style());
        let text_color = visuals.text_color();
        let screen = |p: [f64; 3]| to_screen(view_proj, rect, p);
        let line = |a: [f64; 3], b: [f64; 3]| {
            if let (Some(a), Some(b)) = (screen(a), screen(b)) {
                painter.line_segment([a, b], stroke);
            }
        };
        for a in [-1., 1.] {
            for b in [-1., 1.] {
                line([-1., a, b], [1., a, b]);
                line([a, -1., b], [a, 1., b]);
                line([a, b, -1.], [a, b, 1.]);
            }
        }
        let center = screen([0., 0., 0.]).unwrap_or(rect.center());
        let label = |p: [f64; 3], text: String| {
            if let Some(position) = screen(p) {
                let away = (position - center).normalized();
                painter.text(
                    position + away * LABEL_GAP,
                    egui::Align2::CENTER_CENTER,
                    text,
                    font.clone(),
                    text_color,
                );
            }
        };
        // The bottom edges along x and y on the side of the camera, the vertical edge furthest left
        let eye = self.camera.eye();
        let (sx, sy) = (eye[0].signum(), eye[1].signum());
        let domain = self.camera.domain();
        let step = nice_step(2. * self.camera.radius);
        let ticks = |min: f64, max: f64, step: f64| {
            let first = (min / step).ceil() as i64;
            let last = (max / step).floor() as i64;
            (first..=last).map(move |k| k as f64 * step)
        };
        let normalized = |value: f64, min: f64, max: f64| 2. * (value - min) / (max - min) - 1.;
        for x in ticks(domain[0], domain[1], step) {
            label(
                [normalized(x, domain[0], domain[1]), sy, -1.],
                format_number(x),
            );
        }
        for y in ticks(domain[2], domain[3], step) {
            label(
                [sx, normalized(y, domain[2], domain[3]), -1.],
                format_number(y),
            );
        }
        let corner = [[-1., -1.], [-1., 1.], [1., -1.], [1., 1.]]
            .into_iter()
            .min_by(|a, b| {
                let x = |p: &[f64; 2]| screen([p[0], p[1], 0.]).map_or(f32::INFINITY, |p| p.x);
                x(a).total_cmp(&x(b))
            })
            .unwrap_or([-1., -1.]);
        let [z_min, z_max] = range;
        for z in ticks(z_min, z_max, nice_step(z_max - z_min)) {
            label(
                [corner[0], corner[1], normalized(z, z_min, z_max)],
                format_number(z),
            );
        }
        label([0., sy * 1.25, -1.], "x".to_owned());
        label([sx * 1.25, 0., -1.], "y".to_owned());
        label([corner[0], corner[1], 1.2], "z".to_owned());
    }
}

/// The height range from sampled `heights`: from the 2nd to the 98th percentile of the finite ones, padded, or
/// `[-radius, radius]` without any.
fn height_range(mut heights: Vec<f64>, radius: f64) -> [f64; 2] {
    heights.retain(|value| value.is_finite());
    if heights.is_empty() {
        return [-radius, radius];
    }
    heights.sort_by(f64::total_cmp);
    let last = heights.len() - 1;
    #[allow(
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        clippy::cast_precision_loss
    )]
    let at = |q: f64| heights[(q * last as f64).round() as usize];
    let (low, high) = (at(0.02), at(0.98));
    let pad = if high > low {
        (high - low) * 0.1
    } else {
        low.abs().max(1.) * 0.5
    };
    [low - pad, high + pad]
}

/// The uniforms of the shader of the surface `drawable`, see [`crate::shader::SURFACE`].
#[allow(clippy::cast_possible_truncation)]
fn uniforms(
    camera: &Camera,
    view_proj: &Mat4,
    range: [f64; 2],
    drawable: &Drawable<'_>,
    linear: bool,
) -> Box<[f32; SURFACE_UNIFORMS]> {
    let mut uniforms = Box::new([0.; SURFACE_UNIFORMS]);
    // By columns
    for column in 0..4 {
        for row in 0..4 {
            uniforms[column * 4 + row] = view_proj[row][column] as f32;
        }
    }
    let domain = camera.domain();
    let color = color(drawable.color, linear);
    // A light above the camera
    let eye = camera.eye();
    let light = [eye[0], eye[1], eye[2] + DISTANCE];
    let norm = light.iter().map(|c| c * c).sum::<f64>().sqrt();
    uniforms[16..32].copy_from_slice(&[
        domain[0] as f32,
        domain[1] as f32,
        domain[2] as f32,
        domain[3] as f32,
        range[0] as f32,
        range[1] as f32,
        RESOLUTION as f32,
        nice_step(2. * camera.radius) as f32,
        color[0],
        color[1],
        color[2],
        1.,
        (light[0] / norm) as f32,
        (light[1] / norm) as f32,
        (light[2] / norm) as f32,
        if linear { 1. } else { 0. },
    ]);
    for (uniform, value) in uniforms[32..].iter_mut().zip(&drawable.params) {
        *uniform = *value as f32;
    }
    uniforms
}

#[cfg(test)]
mod tests {
    use eframe::{
        egui::Color32,
        egui_wgpu::{CallbackTrait as _, wgpu},
    };
    use formalith_session::Session;

    use super::*;
    use crate::gpu::{scene::SceneResources, tests::device};

    #[test]
    fn test_projection() {
        let camera = Camera::default();
        let m = camera.view_proj(1.5);
        let [x, y, z, w] = project(&m, [0., 0., 0.]);
        assert!(w > 0. && (x / w).abs() < 1e-12 && (y / w).abs() < 1e-12);
        assert!((0.0..1.).contains(&(z / w)));
        // Every corner of the box is in view
        for corner in [[-1., -1., -1.], [1., 1., 1.], [1., -1., 1.], [-1., 1., -1.]] {
            let [x, y, _, w] = project(&m, corner);
            assert!((x / w).abs() < 1. && (y / w).abs() < 1., "{corner:?}");
        }
        assert_eq!(nice_step(10.), 2.);
        assert_eq!(height_range(vec![f64::NAN], 3.), [-3., 3.]);
        let [low, high] = height_range((0..=100).map(f64::from).collect(), 1.);
        assert!(low < 2. && high > 98. && high < 120.);
    }

    #[test]
    fn test_hit() {
        let (_, graph) = Session::new().graph("x^2 + y^2");
        let graph = graph.unwrap();
        let drawable = Drawable {
            id: 0,
            revision: 0,
            graph: &graph,
            color: Color32::WHITE,
            params: vec![],
            name: String::new(),
            complex_view: crate::plot::ComplexView::default(),
        };
        let space = Space {
            camera: Camera {
                center: [1., 2.],
                ..Camera::default()
            },
            ..Space::default()
        };
        let rect = egui::Rect::from_min_size(Pos2::ZERO, egui::vec2(300., 200.));
        let range = [0., 60.];
        // The point of the surface projected under the pointer is found back
        let m = space.camera.view_proj(1.5);
        for [x, y] in [[1., 2.], [3., 0.], [-2., 4.]] {
            let z = 2. * (x * x + y * y) / 60. - 1.;
            let normalized = [(x - 1.) / 5., (y - 2.) / 5., z];
            let pointer = to_screen(&m, rect, normalized).unwrap();
            let [hx, hy] = space.hit(&[&drawable], range, rect, pointer).unwrap();
            assert!(
                (hx - x).abs() < 1e-3 && (hy - y).abs() < 1e-3,
                "{x}, {y}: {hx}, {hy}"
            );
        }
        // Nothing outside of the box
        assert!(
            space
                .hit(&[&drawable], range, rect, Pos2::new(1., 1.))
                .is_none()
        );
    }

    const SIZE: u32 = 128;

    /// The opacity of the pixels of the graph of `line` seen from above, drawn offscreen.
    fn draw(device: &(wgpu::Adapter, wgpu::Device, wgpu::Queue), line: &str) -> Vec<f32> {
        let (_, device, queue) = device;
        let (_, graph) = Session::new().graph(line);
        let graph = graph.expect("A graph");
        let drawable = Drawable {
            id: 0,
            revision: 0,
            graph: &graph,
            color: Color32::WHITE,
            params: vec![],
            name: String::new(),
            complex_view: crate::plot::ComplexView::default(),
        };
        let camera = Camera {
            yaw: 0.,
            pitch: 1.5,
            ..Camera::default()
        };
        let view_proj = camera.view_proj(1.);
        let mut space = Space::new(Some(false));
        let shader = space.shader(&drawable).expect("A surface");
        let callback = SceneCallback {
            frame: 1,
            size: [SIZE, SIZE],
            surfaces: vec![SurfaceDraw {
                id: 0,
                shader,
                uniforms: uniforms(&camera, &view_proj, [-1., 51.], &drawable, false),
            }],
        };
        let format = wgpu::TextureFormat::Rgba8Unorm;
        let mut resources = egui_wgpu::CallbackResources::default();
        resources.insert(SceneResources::new(device, format));
        let texture = device.create_texture(&wgpu::TextureDescriptor {
            label: None,
            size: wgpu::Extent3d {
                width: SIZE,
                height: SIZE,
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
            size_in_pixels: [SIZE, SIZE],
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
            let rect = egui::Rect::from_min_size(Pos2::ZERO, egui::vec2(SIZE as f32, SIZE as f32));
            let info = egui::PaintCallbackInfo {
                viewport: rect,
                clip_rect: rect,
                pixels_per_point: 1.,
                screen_size_px: [SIZE, SIZE],
            };
            callback.paint(info, &mut pass.forget_lifetime(), &resources);
        }
        let staging = device.create_buffer(&wgpu::BufferDescriptor {
            label: None,
            size: u64::from(SIZE * SIZE * 4),
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        encoder.copy_texture_to_buffer(
            texture.as_image_copy(),
            wgpu::TexelCopyBufferInfo {
                buffer: &staging,
                layout: wgpu::TexelCopyBufferLayout {
                    offset: 0,
                    bytes_per_row: Some(SIZE * 4),
                    rows_per_image: None,
                },
            },
            texture.size(),
        );
        queue.submit([encoder.finish()]);
        staging.map_async(wgpu::MapMode::Read, .., |result| result.expect("Mapped"));
        let _ = device.poll(wgpu::PollType::wait_indefinitely());
        let data = staging.get_mapped_range(..).expect("Mapped").to_vec();
        data.chunks(4)
            .map(|pixel| f32::from(pixel[3]) / 255.)
            .collect()
    }

    #[test]
    fn test_render() {
        let Some(device) = device() else {
            eprintln!("No GPU, skipped");
            return;
        };
        let at = |image: &[f32], column: u32, row: u32| image[(row * SIZE + column) as usize];
        // Inside the range `[0, 50]` over the whole domain: seen from above, the middle is covered, the corners of
        // the view (out of the box) aren't
        let image = draw(&device, "x^2 + y^2");
        assert!(at(&image, SIZE / 2, SIZE / 2) > 0.99);
        assert!(at(&image, 1, 1) == 0.);
        // Undefined everywhere
        let image = draw(&device, "sqrt(-1 - x^2 - y^2)");
        assert!(image.iter().all(|alpha| *alpha == 0.));
        // A complex function
        let mut session = Session::new();
        session.run(":set C");
        let (_, graph) = session.graph("z^2 + 1");
        assert!(matches!(graph.unwrap().kind, GraphKind::ComplexMap { .. }));
    }
}
