// Draws the images under a complex function `f = U + i V` (`U` and `V` of `x = Re z`, `y = Im z`, emitted after this
// template) of the lines `Im z = k` (in `color`) and `Re z = k` (in `fill`) for integers `k` from `-K` to `K`, `z`
// moving between `-K` and `K` along them. Each instance is a line, cut into `SEGMENTS` segments drawn as quads;
// segments through a pole or with an undefined end are dropped.
// With the kind 5, it draws instead a single line: the path `(U(t), V(t))` of a function of a real `t` from `-K` to
// `K`, `U` and `V` being evaluated with `y` undefined.

struct Uniforms {
    // `x_min`, `x_max`, `y_min`, `y_max`
    view: vec4<f32>,
    // Width and height of the plot in pixels, half the width of lines in pixels, the kind of graph (4, or 5 for a path)
    frame: vec4<f32>,
    // Premultiplied colors of the two families of lines
    color: vec4<f32>,
    fill: vec4<f32>,
    flags: vec4<f32>,
    params: array<vec4<f32>, 16>,
}

@group(0) @binding(0) var<uniform> u: Uniforms;

fn param(i: u32) -> f32 {
    return u.params[i / 4u][i % 4u];
}

// The largest `|k|` of the lines, so `2 K + 1` lines per family.
const K: i32 = 10;
// The number of segments of a line, its vertices being `6 * SEGMENTS`.
const SEGMENTS: u32 = 1024u;

struct VertexOutput {
    @builtin(position) position: vec4<f32>,
    // The signed distance in pixels from the line, across it
    @location(0) across: f32,
    // Half the width of the line in pixels
    @location(1) @interpolate(flat) half_width: f32,
    // The family of the line, 0 or 1
    @location(2) @interpolate(flat) family: u32,
}

// The image in pixels, from the bottom left corner, of the point at the parameter `t` of the line `instance`.
fn image(instance: u32, t: f32) -> vec2<f32> {
    let lines = u32(2 * K + 1);
    let k = f32(i32(instance % lines) - K);
    var w: vec2<f32>;
    if u.frame.w == 5.0 {
        w = vec2<f32>(U(t, nf_nan()), V(t, nf_nan()));
    } else if instance < lines {
        w = vec2<f32>(U(t, k), V(t, k));
    } else {
        w = vec2<f32>(U(k, t), V(k, t));
    }
    return vec2<f32>(
        (w.x - u.view.x) * u.frame.x / (u.view.y - u.view.x),
        (w.y - u.view.z) * u.frame.y / (u.view.w - u.view.z),
    );
}

fn finite(p: vec2<f32>) -> bool {
    return nf_finite(p.x) && nf_finite(p.y);
}

// The segment `[a, b]` clipped to a box around the plot (so that far points keep their precision), as the
// parameters of its ends, or `(1, 0)` when it is outside.
fn clip(a: vec2<f32>, b: vec2<f32>) -> vec2<f32> {
    let margin = 2.0 * max(u.frame.x, u.frame.y);
    let low = vec2<f32>(-margin);
    let high = u.frame.xy + margin;
    var t0 = 0.0;
    var t1 = 1.0;
    let d = b - a;
    for (var i = 0; i < 2; i++) {
        if d[i] == 0.0 {
            if a[i] < low[i] || a[i] > high[i] {
                return vec2<f32>(1.0, 0.0);
            }
        } else {
            var s0 = (low[i] - a[i]) / d[i];
            var s1 = (high[i] - a[i]) / d[i];
            if s0 > s1 {
                let s = s0;
                s0 = s1;
                s1 = s;
            }
            t0 = max(t0, s0);
            t1 = min(t1, s1);
        }
    }
    return vec2<f32>(t0, t1);
}

// The parameter of the end `i` of the segments of a line.
fn parameter(i: u32) -> f32 {
    let range = f32(K);
    return -range + f32(i) * (2.0 * range / f32(SEGMENTS));
}

// The unit normal of the segment from `a` to `b`, `fallback` when they are equal.
fn normal_of(a: vec2<f32>, b: vec2<f32>, fallback: vec2<f32>) -> vec2<f32> {
    let d = b - a;
    if !(length(d) > 0.0) {
        return fallback;
    }
    let direction = normalize(d);
    return vec2<f32>(-direction.y, direction.x);
}

// The offset of the corners at the joint `p` of a segment of normal `n` with the segment towards `other` (before
// `p` if `before`), so that consecutive quads share their edges: a miter, limited for sharp angles.
fn miter(p: vec2<f32>, other: vec2<f32>, n: vec2<f32>, before: bool) -> vec2<f32> {
    if !finite(other) {
        return n;
    }
    var m = n;
    if before {
        m = normal_of(other, p, n) + n;
    } else {
        m = n + normal_of(p, other, n);
    }
    if !(length(m) > 0.0) {
        return n;
    }
    m = normalize(m);
    return m / max(dot(m, n), 0.25);
}

@vertex
fn vs_main(@builtin(vertex_index) index: u32, @builtin(instance_index) instance: u32) -> VertexOutput {
    let lines = u32(2 * K + 1);
    let segment = index / 6u;
    let corner = index % 6u;
    var a = image(instance, parameter(segment));
    var b = image(instance, parameter(segment + 1u));
    let middle = image(instance, 0.5 * (parameter(segment) + parameter(segment + 1u)));

    var out: VertexOutput;
    out.family = instance / lines;
    var half_width = u.frame.z;
    if u.frame.w != 5.0 && i32(instance % lines) == K {
        half_width *= 1.6;
    }
    out.half_width = half_width;
    out.across = 0.0;
    out.position = vec4<f32>(2.0, 2.0, 0.0, 1.0);

    // Undefined ends, or a pole between them: the image of the middle is far from the chord
    let chord = length(b - a);
    if !finite(a) || !finite(b) || !finite(middle)
        || (chord > 4.0 && length(middle - 0.5 * (a + b)) > chord) {
        return out;
    }
    let clipped = clip(a, b);
    if clipped.x >= clipped.y {
        return out;
    }
    let n = normal_of(a, b, vec2<f32>(0.0, 1.0));
    let extent = half_width + 1.0;
    // Joints with the neighboring segments, unless an end is clipped or the first or last one
    var start = n;
    if clipped.x == 0.0 && segment > 0u {
        start = miter(a, image(instance, parameter(segment - 1u)), n, true);
    }
    var end = n;
    if clipped.y == 1.0 && segment + 1u < SEGMENTS {
        end = miter(b, image(instance, parameter(segment + 2u)), n, false);
    }
    let d = b - a;
    b = a + clipped.y * d;
    a = a + clipped.x * d;
    var p: vec2<f32>;
    var side: f32;
    switch corner {
        case 0u: { p = a; side = -1.0; }
        case 1u: { p = b; side = -1.0; }
        case 2u: { p = a; side = 1.0; }
        case 3u: { p = a; side = 1.0; }
        case 4u: { p = b; side = -1.0; }
        default: { p = b; side = 1.0; }
    }
    if corner == 0u || corner == 2u || corner == 3u {
        p += start * side * extent;
    } else {
        p += end * side * extent;
    }
    out.across = side * extent;
    out.position = vec4<f32>(p / u.frame.xy * 2.0 - 1.0, 0.0, 1.0);
    return out;
}

@fragment
fn fs_main(in: VertexOutput) -> @location(0) vec4<f32> {
    let coverage = clamp(in.half_width + 0.5 - abs(in.across), 0.0, 1.0);
    if in.family == 0u {
        return u.color * coverage;
    }
    return u.fill * coverage;
}
