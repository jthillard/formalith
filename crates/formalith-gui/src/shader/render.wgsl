// Draws the graph of `F` (emitted after this template) in the whole plot, each fragment evaluating `F` around
// itself: curves `y = F(x)` and `x = F(y)` from a few samples per pixel, `F(x, y) = 0` from the sign of `F` around
// the pixel, regions from its sign at the pixel.

struct Uniforms {
    // `x_min`, `x_max`, `y_min`, `y_max`
    view: vec4<f32>,
    // Width and height of the plot in pixels, half the width of lines in pixels, the kind of graph (0: `y = F(x)`,
    // 1: `x = F(y)`, 2: `F(x, y)` compared with 0)
    frame: vec4<f32>,
    // Premultiplied colors
    color: vec4<f32>,
    fill: vec4<f32>,
    // The comparison (0: `=`, 1: `<`, 2: `<=`, 3: `>`, 4: `>=`), 1 if the boundary is dashed, the period of dashes in
    // pixels
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

// The coordinate along the independent axis at the pixel coordinate `a` (from the left or the bottom).
fn along_value(a: f32) -> f32 {
    if u.frame.w == 0.0 {
        return u.view.x + a * (u.view.y - u.view.x) / u.frame.x;
    }
    return u.view.z + a * (u.view.w - u.view.z) / u.frame.y;
}

// The value of the curve at the pixel coordinate `a`, in pixels from the left or the bottom.
fn curve_at(a: f32) -> f32 {
    let t = along_value(a);
    if u.frame.w == 0.0 {
        return (F(t, nf_nan()) - u.view.z) * u.frame.y / (u.view.w - u.view.z);
    }
    return (F(nf_nan(), t) - u.view.x) * u.frame.x / (u.view.y - u.view.x);
}

// The distance from `p` to the segment `[a, b]`.
fn segment_distance(p: vec2<f32>, a: vec2<f32>, b: vec2<f32>) -> f32 {
    let ab = b - a;
    let len2 = dot(ab, ab);
    var t = 0.0;
    if len2 > 0.0 {
        t = clamp(dot(p - a, ab) / len2, 0.0, 1.0);
    }
    return length(p - (a + t * ab));
}

// Number of bisections looking for the border of the domain or a discontinuity.
const BISECTIONS: i32 = 12;

// The distance in pixels from the pixel at `(a, c)` (along and across the independent axis) to the curve, from
// samples one pixel apart, cut at undefined values and discontinuities.
fn curve_distance(a: f32, c: f32, extent: f32) -> f32 {
    let w = u.frame.z;
    let low = -4.0 * extent;
    let high = 5.0 * extent;
    var best = 1e30;
    var a0 = a - 3.0;
    var v0 = curve_at(a0);
    for (var k = -2; k <= 3; k++) {
        let a1 = a + f32(k);
        let v1 = curve_at(a1);
        var p0 = vec2<f32>(a0, v0);
        var p1 = vec2<f32>(a1, v1);
        var draw = true;
        let d0 = nf_finite(v0);
        let d1 = nf_finite(v1);
        if !d0 && !d1 {
            draw = false;
        } else if d0 != d1 {
            // The border of the domain
            var lo = select(a1, a0, d0);
            var hi = select(a0, a1, d0);
            var v_lo = select(v1, v0, d0);
            for (var i = 0; i < BISECTIONS; i++) {
                let mid = 0.5 * (lo + hi);
                let v_mid = curve_at(mid);
                if nf_finite(v_mid) {
                    lo = mid;
                    v_lo = v_mid;
                } else {
                    hi = mid;
                }
            }
            let defined = select(p1, p0, d0);
            p0 = defined;
            p1 = vec2<f32>(lo, v_lo);
        } else {
            let top = max(v0, v1);
            let bottom = min(v0, v1);
            if c < bottom - w - 1.0 || c > top + w + 1.0 {
                draw = false;
            } else if top - bottom > 2.0 {
                // A steep segment: continuous if the jump shrinks when following it, else a pole or a step
                let jump = top - bottom;
                var lo = a0;
                var hi = a1;
                var v_lo = v0;
                var v_hi = v1;
                for (var i = 0; i < 10; i++) {
                    let mid = 0.5 * (lo + hi);
                    let v_mid = curve_at(mid);
                    if !nf_finite(v_mid) {
                        break;
                    }
                    if abs(v_mid - v_lo) > abs(v_hi - v_mid) {
                        hi = mid;
                        v_hi = v_mid;
                    } else {
                        lo = mid;
                        v_lo = v_mid;
                    }
                }
                let rest = abs(v_hi - v_lo);
                if !nf_finite(rest) || rest > 0.25 * jump {
                    draw = false;
                }
            }
        }
        if draw {
            p0.y = clamp(p0.y, low, high);
            p1.y = clamp(p1.y, low, high);
            best = min(best, segment_distance(vec2<f32>(a, c), p0, p1));
        }
        a0 = a1;
        v0 = v1;
    }
    return best;
}

// Whether the comparison of the graph holds for `value`.
fn holds(value: f32) -> bool {
    let relation = u.flags.x;
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

// The coverage of the curve `F(x, y) = 0` at the pixel `p` (from the bottom left), from `F` at the center `value`
// and at the corners of a box around it.
fn contour_coverage(p: vec2<f32>, x: f32, y: f32, value: f32) -> f32 {
    let w = u.frame.z;
    let h = w + 0.5;
    let sx = (u.view.y - u.view.x) / u.frame.x;
    let sy = (u.view.w - u.view.z) / u.frame.y;
    let f_pp = F(x + h * sx, y + h * sy);
    let f_pm = F(x + h * sx, y - h * sy);
    let f_mp = F(x - h * sx, y + h * sy);
    let f_mm = F(x - h * sx, y - h * sy);
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
    if u.flags.y != 0.0 {
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
    if u.frame.w == 0.0 {
        let coverage = clamp(u.frame.z + 0.5 - curve_distance(p.x, p.y, u.frame.y), 0.0, 1.0);
        return u.color * coverage;
    }
    if u.frame.w == 1.0 {
        let coverage = clamp(u.frame.z + 0.5 - curve_distance(p.y, p.x, u.frame.x), 0.0, 1.0);
        return u.color * coverage;
    }
    let x = u.view.x + p.x * (u.view.y - u.view.x) / u.frame.x;
    let y = u.view.z + p.y * (u.view.w - u.view.z) / u.frame.y;
    let value = F(x, y);
    var background = vec4<f32>(0.0);
    if u.flags.x != 0.0 && holds(value) {
        background = u.fill;
    }
    let coverage = contour_coverage(p, x, y, value);
    return u.color * coverage + background * (1.0 - coverage);
}
