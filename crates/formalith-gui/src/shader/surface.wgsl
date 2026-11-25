// Draws a surface over the domain of the 3D view, an `N × N` grid of quads without vertex buffer, each vertex
// evaluating `surface_value(x, y)` (emitted after this template with `COMPLEX`): its height, and for a complex function
// the direction `f / |f|` of its value, giving the hue. Coordinates are normalized to the box `[-1, 1]^3`, then
// projected by `u.view_proj`; parts outside of the box and triangles touching undefined points are discarded.

struct Uniforms {
    // From the box `[-1, 1]^3` to clip space
    view_proj: mat4x4<f32>,
    // `x_min`, `x_max`, `y_min`, `y_max`
    domain: vec4<f32>,
    // `z_min`, `z_max`, the number of quads along each side, the step of the grid lines
    range: vec4<f32>,
    // Opaque color of a real surface
    color: vec4<f32>,
    // The direction of the light in the box, whether colors are written in linear space (1) or not (0)
    light: vec4<f32>,
    params: array<vec4<f32>, 16>,
}

@group(0) @binding(0) var<uniform> u: Uniforms;

fn param(i: u32) -> f32 {
    return u.params[i / 4u][i % 4u];
}

struct VertexOutput {
    @builtin(position) position: vec4<f32>,
    // The point in the box
    @location(0) normalized: vec3<f32>,
    // The point `(x, y)` of the domain
    @location(1) xy: vec2<f32>,
    // The direction of a complex value
    @location(2) phase: vec2<f32>,
    // 1 where the surface is defined, 0 elsewhere
    @location(3) valid: f32,
}

@vertex
fn vs_main(@builtin(vertex_index) index: u32) -> VertexOutput {
    let n = u32(u.range.z);
    let cell = index / 6u;
    let corner = index % 6u;
    // Two triangles per quad
    let dx = select(0u, 1u, corner == 1u || corner == 4u || corner == 5u);
    let dy = select(0u, 1u, corner == 2u || corner == 3u || corner == 5u);
    let s = f32(cell % n + dx) / f32(n);
    let t = f32(cell / n + dy) / f32(n);
    let x = mix(u.domain.x, u.domain.y, s);
    let y = mix(u.domain.z, u.domain.w, t);
    let value = surface_value(x, y);
    let valid = nf_finite(value.x);
    // Heights far out of the box are clamped, so that poles don't stretch the triangles around them
    let height = 2.0 * (value.x - u.range.x) / (u.range.y - u.range.x) - 1.0;
    let z = select(0.0, clamp(height, -2.0, 2.0), valid);
    var out: VertexOutput;
    out.normalized = vec3<f32>(2.0 * s - 1.0, 2.0 * t - 1.0, z);
    out.position = u.view_proj * vec4<f32>(out.normalized, 1.0);
    out.xy = vec2<f32>(x, y);
    out.phase = select(vec2<f32>(1.0, 0.0), value.yz, nf_finite(value.y) && nf_finite(value.z));
    out.valid = select(0.0, 1.0, valid);
    return out;
}

// The color of the hue `h` in `[0, 1)`, saturated.
fn hue(h: f32) -> vec3<f32> {
    let k = vec3<f32>(5.0, 3.0, 1.0);
    let p = abs(fract(vec3<f32>(h) + k / 6.0) * 6.0 - 3.0);
    return mix(vec3<f32>(1.0), clamp(p - 1.0, vec3<f32>(0.0), vec3<f32>(1.0)), 0.8);
}

// How much the point is on a grid line, from its coordinate `c` in steps.
fn grid_line(c: f32) -> f32 {
    let distance = abs(fract(c - 0.5) - 0.5) / max(fwidth(c), 1e-6);
    return 1.0 - min(distance, 1.0);
}

@fragment
fn fs_main(in: VertexOutput) -> @location(0) vec4<f32> {
    // Derivatives first, in uniform control flow
    let normal = normalize(cross(dpdx(in.normalized), dpdy(in.normalized)));
    let step = u.range.w;
    let line = max(grid_line(in.xy.x / step), grid_line(in.xy.y / step));
    if in.valid < 0.999 || abs(in.normalized.z) > 1.0 {
        discard;
    }
    var base = u.color.rgb;
    if COMPLEX {
        let turn = atan2(in.phase.y, in.phase.x) / 6.2831853;
        base = hue(fract(turn));
        if u.light.w > 0.5 {
            base = pow(base, vec3<f32>(2.2));
        }
    }
    let diffuse = abs(dot(normal, u.light.xyz));
    let shade = (0.35 + 0.65 * diffuse) * (1.0 - 0.3 * line);
    return vec4<f32>(base * shade, 1.0);
}
