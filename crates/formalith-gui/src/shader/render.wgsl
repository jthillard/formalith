// Draws the graph of the relations `F_at(i, x, y) op 0` holding together (emitted after this template, with
// `relation_of` and `COUNT`) in the whole plot, each fragment evaluating them around itself: curves `F_i(x, y) = 0`
// from the sign of `F_i` around the pixel, regions from their signs at the pixel. Curves `y = f(x)` are sampled on
// the CPU instead.

struct Uniforms {
    // `x_min`, `x_max`, `y_min`, `y_max`
    view: vec4<f32>,
    // Width and height of the plot in pixels, half the width of lines in pixels, unused
    frame: vec4<f32>,
    // Premultiplied colors
    color: vec4<f32>,
    fill: vec4<f32>,
    // Unused, unused, the period of dashes of strict boundaries in pixels, unused
    flags: vec4<f32>,
    params: array<vec4<f32>, 16>,
}

@group(0) @binding(0) var<uniform> u: Uniforms;

fn param(i: u32) -> f32 {
    return u.params[i / 4u][i % 4u];
}

struct VertexOutput {
    @builtin(position) position: vec4<f32>,
    // From the top left corner (0, 0) to the bottom right one (1, 1)
    @location(0) uv: vec2<f32>,
}

// A triangle covering the plot.
@vertex
fn vs_main(@builtin(vertex_index) index: u32) -> VertexOutput {
    let p = vec2<f32>(f32((index << 1u) & 2u), f32(index & 2u));
    var out: VertexOutput;
    out.position = vec4<f32>(p * 2.0 - 1.0, 0.0, 1.0);
    out.uv = vec2<f32>(p.x, 1.0 - p.y);
    return out;
}

// Whether the comparison of the relation `i` (0: `=`, 1: `<`, 2: `<=`, 3: `>`, 4: `>=`) holds for `value`.
fn holds(i: u32, value: f32) -> bool {
    let relation = relation_of(i);
    if relation == 1.0 {
        return value < 0.0;
    }
    if relation == 2.0 {
        return value <= 0.0;
    }
    if relation == 3.0 {
        return value > 0.0;
    }
    if relation == 4.0 {
        return value >= 0.0;
    }
    return false;
}

// Whether every relation which isn't an equation holds at `(x, y)`, except `skip`.
fn others_hold(skip: u32, x: f32, y: f32) -> bool {
    for (var j = 0u; j < COUNT; j++) {
        if j != skip && relation_of(j) != 0.0 && !holds(j, F_at(j, x, y)) {
            return false;
        }
    }
    return true;
}

// The coverage of the curve `F_i(x, y) = 0` at the pixel `p` (from the bottom left), from `F_i` at the center
// `value` and at the corners of a box around it.
fn contour_coverage(i: u32, p: vec2<f32>, x: f32, y: f32, value: f32) -> f32 {
    let w = u.frame.z;
    let h = w + 0.5;
    let sx = (u.view.y - u.view.x) / u.frame.x;
    let sy = (u.view.w - u.view.z) / u.frame.y;
    let f_pp = F_at(i, x + h * sx, y + h * sy);
    let f_pm = F_at(i, x + h * sx, y - h * sy);
    let f_mp = F_at(i, x - h * sx, y + h * sy);
    let f_mm = F_at(i, x - h * sx, y - h * sy);
    if !(nf_finite(value) && nf_finite(f_pp) && nf_finite(f_pm) && nf_finite(f_mp) && nf_finite(f_mm)) {
        return 0.0;
    }
    let lowest = min(min(min(f_pp, f_pm), min(f_mp, f_mm)), value);
    let highest = max(max(max(f_pp, f_pm), max(f_mp, f_mm)), value);
    if !(lowest < 0.0 && highest > 0.0) && value != 0.0 {
        return 0.0;
    }
    // Near a pole, the value at the crossing is large rather than 0
    let largest = max(max(abs(f_pp), abs(f_pm)), max(abs(f_mp), abs(f_mm)));
    if abs(value) > largest {
        return 0.0;
    }
    let gradient = vec2<f32>((f_pp + f_pm) - (f_mp + f_mm), (f_pp + f_mp) - (f_pm + f_mm)) / (4.0 * h);
    let norm = length(gradient);
    if !(norm > 0.0) || !nf_finite(norm) {
        return 0.0;
    }
    let distance = abs(value) / norm;
    var coverage = clamp(w + 0.5 - distance, 0.0, 1.0);
    let relation = relation_of(i);
    if relation == 1.0 || relation == 3.0 {
        // Dashes by the coordinate along the axis closest to the tangent `(-gradient.y, gradient.x)`, which
        // changes at the same rate everywhere on the curve, unlike a projection on the tangent
        let along = select(p.y, p.x, abs(gradient.y) > abs(gradient.x));
        if fract(along / u.flags.z) > 0.55 {
            coverage = 0.0;
        }
    }
    return coverage;
}

@fragment
fn fs_main(in: VertexOutput) -> @location(0) vec4<f32> {
    let pixel = in.uv * u.frame.xy;
    // From the bottom left corner
    let p = vec2<f32>(pixel.x, u.frame.y - pixel.y);
    let x = u.view.x + p.x * (u.view.y - u.view.x) / u.frame.x;
    let y = u.view.z + p.y * (u.view.w - u.view.z) / u.frame.y;
    let inside = others_hold(COUNT, x, y);
    // With equations, their common points where the other relations hold
    var equations = false;
    var on_curves = 1.0;
    for (var i = 0u; i < COUNT; i++) {
        if relation_of(i) == 0.0 {
            equations = true;
            on_curves = min(on_curves, contour_coverage(i, p, x, y, F_at(i, x, y)));
        }
    }
    if equations {
        return u.color * select(0.0, on_curves, inside);
    }
    // Else a region, bounded by the boundary of each relation where the other ones hold
    var background = vec4<f32>(0.0);
    if inside {
        background = u.fill;
    }
    var coverage = 0.0;
    for (var i = 0u; i < COUNT; i++) {
        if others_hold(i, x, y) {
            coverage = max(coverage, contour_coverage(i, p, x, y, F_at(i, x, y)));
        }
    }
    return u.color * coverage + background * (1.0 - coverage);
}
