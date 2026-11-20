// Remarkable points of a curve `y = f(x)` on `[a, b]`, with `objective(mode, x)` (emitted after this template) giving
// the function whose zeros are searched: `f` (roots), `f'` (extrema), `f - g_k` (intersections). A port of the
// former CPU search: `sample` evaluates the objectives and their scales, `refine` finds a zero on each interval.

struct Config {
    a: f32,
    step: f32,
    // The step of finite differences
    h: f32,
    // The number of intervals
    n: u32,
    modes: u32,
}

@group(0) @binding(0) var<uniform> cfg: Config;
@group(0) @binding(1) var<storage, read> params: array<f32>;
@group(0) @binding(2) var<storage, read_write> values: array<f32>;
// The largest finite `|value|` of each target, as bits
@group(0) @binding(3) var<storage, read_write> scales: array<atomic<u32>>;
// `(kind, x, y, mode)`, kinds being 1: root, 2: minimum, 3: maximum, 4: intersection
@group(0) @binding(4) var<storage, read_write> points: array<vec4<f32>>;
// The number of points, then the number of zeros of each objective
@group(0) @binding(5) var<storage, read_write> counters: array<atomic<u32>>;

fn param(i: u32) -> f32 {
    return params[i];
}

@compute @workgroup_size(64)
fn sample(@builtin(global_invocation_id) id: vec3<u32>) {
    if id.x > cfg.n || id.y >= cfg.modes {
        return;
    }
    let v = objective(id.y, cfg.a + f32(id.x) * cfg.step);
    values[id.y * (cfg.n + 1u) + id.x] = v;
    if nf_finite(v) {
        atomicMax(&scales[id.y], bitcast<u32>(abs(v)));
    }
}

// A zero of the objective in `[x0, x1]`, where it changes its sign, `y0` being its value at `x0`.
fn bisect(mode: u32, x0_: f32, y0: f32, x1_: f32) -> f32 {
    var x0 = x0_;
    var x1 = x1_;
    for (var i = 0; i < 64; i++) {
        let mid = 0.5 * (x0 + x1);
        if mid == x0 || mid == x1 {
            break;
        }
        let y = objective(mode, mid);
        if y == 0.0 {
            return mid;
        }
        if sign(y) == sign(y0) {
            x0 = mid;
        } else {
            x1 = mid;
        }
    }
    return 0.5 * (x0 + x1);
}

// The minimum of `|objective|` in `[a, b]`, by golden section search.
fn golden_minimum(mode: u32, a_: f32, b_: f32) -> f32 {
    let ratio = 0.6180339887498949;
    var a = a_;
    var b = b_;
    var c = b - ratio * (b - a);
    var d = a + ratio * (b - a);
    for (var i = 0; i < 60; i++) {
        if abs(objective(mode, c)) < abs(objective(mode, d)) {
            b = d;
        } else {
            a = c;
        }
        c = b - ratio * (b - a);
        d = a + ratio * (b - a);
    }
    return 0.5 * (a + b);
}

fn push(point: vec4<f32>) {
    let index = atomicAdd(&counters[0], 1u);
    points[index] = point;
}

@compute @workgroup_size(64)
fn refine(@builtin(global_invocation_id) id: vec3<u32>) {
    let k = id.x;
    let mode = id.y;
    if k >= cfg.n || mode >= cfg.modes {
        return;
    }
    let base = mode * (cfg.n + 1u);
    let x0 = cfg.a + f32(k) * cfg.step;
    let x1 = cfg.a + f32(k + 1u) * cfg.step;
    let y0 = values[base + k];
    let y1 = values[base + k + 1u];
    if !(nf_finite(y0) && nf_finite(y1)) {
        return;
    }
    var scale = bitcast<f32>(atomicLoad(&scales[mode]));
    if !(scale > 0.0) {
        scale = 1.0;
    }
    let epsilon = 1e-3 * scale;
    var found = false;
    var z = 0.0;
    if y0 == 0.0 {
        z = x0;
        found = true;
    } else if sign(y0) != sign(y1) && y1 != 0.0 {
        let root = bisect(mode, x0, y0, x1);
        // A pole changes the sign with large values
        if abs(objective(mode, root)) <= max(abs(y0), abs(y1)) {
            z = root;
            found = true;
        }
    } else if k > 0u {
        // A local minimum of `|objective|` close to 0, like the root of `x^2`
        let y_prev = values[base + k - 1u];
        if nf_finite(y_prev) && abs(y0) < abs(y_prev) && abs(y0) < abs(y1) && abs(y0) < epsilon {
            let x = golden_minimum(mode, x0 - cfg.step, x1);
            if abs(objective(mode, x)) < epsilon * 1e-3 {
                z = x;
                found = true;
            }
        }
    }
    if !found {
        return;
    }
    atomicAdd(&counters[1u + mode], 1u);
    if mode == 0u {
        push(vec4<f32>(1.0, z, 0.0, 0.0));
        return;
    }
    let y = f(z);
    if !nf_finite(y) {
        return;
    }
    if mode == 1u {
        let d = 0.1 * cfg.step;
        let left = f(z - d);
        let right = f(z + d);
        if !(nf_finite(left) && nf_finite(right)) {
            return;
        }
        if left > y && right > y {
            push(vec4<f32>(2.0, z, y, 1.0));
        } else if left < y && right < y {
            push(vec4<f32>(3.0, z, y, 1.0));
        }
        return;
    }
    push(vec4<f32>(4.0, z, y, f32(mode)));
}
