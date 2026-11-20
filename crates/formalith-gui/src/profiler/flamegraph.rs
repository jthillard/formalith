//! A flamegraph of lanes of scopes on a shared time axis: dragged to pan, scrolled or pinched to zoom around the
//! pointer, double clicked to show everything.

use eframe::egui::{self, Ui, vec2};

use super::Lane;

/// The height of a row of scopes, and of the title of a lane.
const ROW_HEIGHT: f32 = 20.;

/// The depth of the scopes of `lane`, the outermost ones being at depth 0.
fn depth(lane: &Lane) -> usize {
    let mut max_depth = 0;
    let mut stack: Vec<(usize, usize)> = lane.roots.iter().map(|&root| (root, 0)).collect();
    while let Some((i, depth)) = stack.pop() {
        max_depth = max_depth.max(depth + 1);
        stack.extend(
            lane.frames[i]
                .children
                .iter()
                .map(|&child| (child, depth + 1)),
        );
    }
    max_depth
}

/// The milliseconds of a duration in nanoseconds.
fn ms(ns: f64) -> f64 {
    ns / 1e6
}

/// Show the flamegraph of `lanes`, whose view is stored under `id`.
pub fn show(lanes: &[Lane], id: egui::Id, ui: &mut Ui) -> egui::Response {
    let lanes: Vec<&Lane> = lanes.iter().filter(|lane| !lane.roots.is_empty()).collect();
    let Some(origin) = lanes
        .iter()
        .filter_map(|lane| lane.range_ns())
        .map(|range| range.0)
        .min()
    else {
        return ui.label("Nothing was recorded.");
    };
    // Times relative to the start, exact in `f64` unlike nanoseconds since the epoch
    let time = |ns: i64| (ns - origin) as f64;
    let end = lanes
        .iter()
        .filter_map(|lane| lane.range_ns())
        .map(|range| time(range.1))
        .fold(0., f64::max);
    let full = (0., if end > 0. { end } else { 1. });

    // The view is stored as fractions of the full range, so it stays valid when the data changes
    let fspan = full.1 - full.0;
    let norm: (f64, f64) = ui.data_mut(|d| d.get_temp(id)).unwrap_or((0.0, 1.0));
    let mut view = (full.0 + norm.0 * fspan, full.0 + norm.1 * fspan);
    if !(view.1 > view.0) || !view.0.is_finite() || !view.1.is_finite() {
        view = full;
    }

    let depths: Vec<usize> = lanes.iter().map(|lane| depth(lane)).collect();
    let rows: usize = depths.iter().map(|depth| depth + 1).sum();
    let size = vec2(ui.available_width(), rows as f32 * ROW_HEIGHT);
    let (resp, painter) = ui.allocate_painter(size, egui::Sense::click_and_drag());
    let rect = resp.rect;
    let w = f64::from(rect.width().max(1.0));

    // Interaction
    let mut span = view.1 - view.0;
    if resp.dragged() {
        let dt = -f64::from(resp.drag_delta().x) / w * span;
        view = (view.0 + dt, view.1 + dt);
    }
    if let Some(p) = resp.hover_pos() {
        let (zoom, scroll) = ui.input(|i| (i.zoom_delta(), i.smooth_scroll_delta.y));
        let z = f64::from(zoom) * (f64::from(scroll) * 0.005).exp();
        if (z - 1.0).abs() > 1e-6 {
            let frac = (f64::from(p.x - rect.left()) / w).clamp(0.0, 1.0);
            let t_cursor = view.0 + frac * span;
            span = (span / z).clamp(fspan * 1e-6, fspan * 10.0);
            view = (t_cursor - frac * span, t_cursor + (1.0 - frac) * span);
        }
    }
    if resp.double_clicked() {
        view = full;
    }
    ui.data_mut(|d| d.insert_temp(id, ((view.0 - full.0) / fspan, (view.1 - full.0) / fspan)));

    let span = view.1 - view.0;
    #[allow(clippy::cast_possible_truncation)]
    let to_x = |t: f64| rect.left() + ((t - view.0) / span) as f32 * rect.width();

    // Drawing
    painter.rect_filled(rect, 0.0, ui.visuals().extreme_bg_color);
    let font = egui::FontId::proportional(12.0);
    let hover = resp.hover_pos();
    let mut hovered: Option<(usize, usize)> = None;
    let mut top = rect.top();
    for (lane_index, (lane, lane_depth)) in lanes.iter().zip(&depths).enumerate() {
        let title =
            egui::Rect::from_min_size(egui::pos2(rect.left(), top), vec2(rect.width(), ROW_HEIGHT));
        painter.rect_filled(title, 0.0, ui.visuals().faint_bg_color);
        painter.text(
            title.left_center() + vec2(4.0, 0.0),
            egui::Align2::LEFT_CENTER,
            &lane.name,
            egui::FontId::proportional(13.0),
            ui.visuals().strong_text_color(),
        );
        let lane_top = top + ROW_HEIGHT;
        let mut stack: Vec<(usize, usize)> = lane.roots.iter().map(|&root| (root, 0)).collect();
        while let Some((i, depth)) = stack.pop() {
            let s = &lane.frames[i];
            let start = time(s.start_ns);
            let end = time(s.end_ns);
            if end < view.0 || start > view.1 {
                continue; // Off-screen: children are inside the parent, skip them too
            }
            let (x0, x1) = (to_x(start).max(rect.left()), to_x(end).min(rect.right()));
            if x1 - x0 < 0.5 {
                continue; // Too thin to see
            }
            let y = lane_top + depth as f32 * ROW_HEIGHT;
            let r = egui::Rect::from_min_max(egui::pos2(x0, y), egui::pos2(x1, y + ROW_HEIGHT))
                .shrink2(vec2(0.5, 0.5));

            let is_hovered = hover.is_some_and(|p| r.contains(p));
            if is_hovered {
                hovered = Some((lane_index, i));
            }
            let mut color = color_for(&s.name);
            if is_hovered {
                color = color.gamma_multiply(1.15);
            }
            painter.rect_filled(r, 2.0, color);
            if r.width() > 24.0 {
                painter.with_clip_rect(r).text(
                    r.left_center() + vec2(3.0, 0.0),
                    egui::Align2::LEFT_CENTER,
                    &s.name,
                    font.clone(),
                    egui::Color32::BLACK,
                );
            }
            stack.extend(s.children.iter().map(|&c| (c, depth + 1)));
        }
        top = lane_top + *lane_depth as f32 * ROW_HEIGHT;
    }

    if let Some((lane, i)) = hovered {
        let s = &lanes[lane].frames[i];
        let start = time(s.start_ns);
        let end = time(s.end_ns);
        resp.clone().on_hover_ui_at_pointer(|ui| {
            ui.strong(&s.name);
            if !s.data.is_empty() {
                ui.monospace(&s.data);
            }
            ui.label(format!("duration: {:.3} ms", ms(end - start)));
            ui.label(format!(
                "start: {:.3} ms  end: {:.3} ms",
                ms(start),
                ms(end)
            ));
        });
    }
    resp
}

/// Stable pastel color derived from the scope name.
fn color_for(name: &str) -> egui::Color32 {
    let mut h: u32 = 2_166_136_261; // FNV-1a
    for b in name.bytes() {
        h = (h ^ u32::from(b)).wrapping_mul(16_777_619);
    }
    #[allow(clippy::cast_precision_loss)]
    egui::ecolor::Hsva::new((h % 360) as f32 / 360.0, 0.45, 0.9, 1.0).into()
}
