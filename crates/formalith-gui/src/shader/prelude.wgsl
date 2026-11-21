// The functions of `Numeric` expressions in f32, ported from `formalith::field::real::numeric`. Undefined values
// are NaN, tested on their bits, and every function checks its domain rather than relying on the GPU.

const PI: f32 = 3.14159265358979;

// The bits go through a variable: a constant NaN or infinity is a shader creation error (WGSL constant expressions
// must be finite), which Chrome reports.
fn nf_nan() -> f32 {
    var bits = 0x7fc00000u;
    return bitcast<f32>(bits);
}

fn nf_inf() -> f32 {
    var bits = 0x7f800000u;
    return bitcast<f32>(bits);
}

// Whether `v` is NaN.
fn nf_undef(v: f32) -> bool {
    return (bitcast<u32>(v) & 0x7fffffffu) > 0x7f800000u;
}

// Whether `v` is neither NaN nor infinite.
fn nf_finite(v: f32) -> bool {
    return (bitcast<u32>(v) & 0x7fffffffu) < 0x7f800000u;
}

// `x^n` for an integer `n`, by squaring.
fn nf_powi(x: f32, n: i32) -> f32 {
    if n == 0 {
        return 1.0;
    }
    var base = x;
    var e = abs(n);
    var result = 1.0;
    loop {
        if (e & 1) != 0 {
            result *= base;
        }
        e = e >> 1u;
        if e == 0 {
            break;
        }
        base *= base;
    }
    if n < 0 {
        return 1.0 / result;
    }
    return result;
}

// `base^exponent`, like `f64::powf`.
fn nf_pow(b: f32, e: f32) -> f32 {
    if e == 0.0 {
        return 1.0;
    }
    if nf_undef(b) || nf_undef(e) {
        return nf_nan();
    }
    if b == 1.0 {
        return 1.0;
    }
    if b == 0.0 {
        if e > 0.0 {
            return 0.0;
        }
        return nf_inf();
    }
    let r = pow(abs(b), e);
    if b < 0.0 {
        if fract(e) != 0.0 {
            return nf_nan();
        }
        if fract(e * 0.5) != 0.0 {
            return -r;
        }
    }
    return r;
}

// `x^(p/q)`, the real root for negative `x` and odd `q`.
fn nf_rpow(x: f32, p: i32, q: i32) -> f32 {
    if q == 1 {
        return nf_powi(x, p);
    }
    if nf_undef(x) {
        return nf_nan();
    }
    let e = f32(p) / f32(q);
    if x == 0.0 {
        if p > 0 {
            return 0.0;
        }
        return nf_inf();
    }
    if x < 0.0 {
        if (q & 1) == 0 {
            return nf_nan();
        }
        let r = pow(-x, e);
        if (p & 1) != 0 {
            return -r;
        }
        return r;
    }
    return pow(x, e);
}

fn nf_exp(x: f32) -> f32 {
    if nf_undef(x) {
        return x;
    }
    if x > 88.8 {
        return nf_inf();
    }
    if x < -104.0 {
        return 0.0;
    }
    return exp(x);
}

fn nf_ln(x: f32) -> f32 {
    if nf_undef(x) || x < 0.0 {
        return nf_nan();
    }
    if x == 0.0 {
        return -nf_inf();
    }
    if !nf_finite(x) {
        return x;
    }
    return log(x);
}

fn nf_sin(x: f32) -> f32 {
    if !nf_finite(x) {
        return nf_nan();
    }
    return sin(x);
}

fn nf_cos(x: f32) -> f32 {
    if !nf_finite(x) {
        return nf_nan();
    }
    return cos(x);
}

fn nf_tan(x: f32) -> f32 {
    if !nf_finite(x) {
        return nf_nan();
    }
    return sin(x) / cos(x);
}

fn nf_asin(x: f32) -> f32 {
    if nf_undef(x) || abs(x) > 1.0 {
        return nf_nan();
    }
    return asin(x);
}

fn nf_acos(x: f32) -> f32 {
    if nf_undef(x) || abs(x) > 1.0 {
        return nf_nan();
    }
    return acos(x);
}

fn nf_atan(x: f32) -> f32 {
    if nf_undef(x) {
        return x;
    }
    return atan(x);
}

fn nf_sinh(x: f32) -> f32 {
    if nf_undef(x) {
        return x;
    }
    if abs(x) < 1e-3 {
        return x + x * x * x / 6.0;
    }
    let e = nf_exp(abs(x));
    return sign(x) * 0.5 * (e - 1.0 / e);
}

fn nf_cosh(x: f32) -> f32 {
    if nf_undef(x) {
        return x;
    }
    let e = nf_exp(abs(x));
    return 0.5 * (e + 1.0 / e);
}

fn nf_tanh(x: f32) -> f32 {
    if nf_undef(x) {
        return x;
    }
    if abs(x) < 1e-3 {
        return x - x * x * x / 3.0;
    }
    let t = exp(-2.0 * abs(x));
    return sign(x) * (1.0 - t) / (1.0 + t);
}

fn nf_asinh(x: f32) -> f32 {
    if nf_undef(x) {
        return x;
    }
    let a = abs(x);
    if a < 1e-3 {
        return x - x * x * x / 6.0;
    }
    if a > 1e18 {
        return sign(x) * (log(a) + 0.693147180559945);
    }
    return sign(x) * log(a + sqrt(a * a + 1.0));
}

fn nf_acosh(x: f32) -> f32 {
    if nf_undef(x) || x < 1.0 {
        return nf_nan();
    }
    if x > 1e18 {
        return log(x) + 0.693147180559945;
    }
    return log(x + sqrt(x * x - 1.0));
}

fn nf_atanh(x: f32) -> f32 {
    if nf_undef(x) || abs(x) > 1.0 {
        return nf_nan();
    }
    if abs(x) == 1.0 {
        return sign(x) * nf_inf();
    }
    if abs(x) < 1e-3 {
        return x + x * x * x / 3.0;
    }
    return 0.5 * log((1.0 + x) / (1.0 - x));
}

fn nf_abs(x: f32) -> f32 {
    return abs(x);
}

fn nf_sign(x: f32) -> f32 {
    if nf_undef(x) {
        return x;
    }
    if x == 0.0 {
        return 0.0;
    }
    return sign(x);
}

fn nf_floor(x: f32) -> f32 {
    if !nf_finite(x) {
        return x;
    }
    return floor(x);
}

fn nf_ceil(x: f32) -> f32 {
    if !nf_finite(x) {
        return x;
    }
    return ceil(x);
}

// The minimum ignoring NaN, like `f64::min`.
fn nf_min(a: f32, b: f32) -> f32 {
    if nf_undef(a) {
        return b;
    }
    if nf_undef(b) {
        return a;
    }
    return min(a, b);
}

fn nf_max(a: f32, b: f32) -> f32 {
    if nf_undef(a) {
        return b;
    }
    if nf_undef(b) {
        return a;
    }
    return max(a, b);
}

// 1 if the comparison holds, 0 otherwise, NaN if a side is undefined.
fn nf_truth(a: f32, b: f32, holds: bool) -> f32 {
    if nf_undef(a) || nf_undef(b) {
        return nf_nan();
    }
    return select(0.0, 1.0, holds);
}

fn nf_lt(a: f32, b: f32) -> f32 {
    return nf_truth(a, b, a < b);
}

fn nf_le(a: f32, b: f32) -> f32 {
    return nf_truth(a, b, a <= b);
}

fn nf_gt(a: f32, b: f32) -> f32 {
    return nf_truth(a, b, a > b);
}

fn nf_ge(a: f32, b: f32) -> f32 {
    return nf_truth(a, b, a >= b);
}

fn nf_eq(a: f32, b: f32) -> f32 {
    return nf_truth(a, b, a == b);
}

fn nf_ne(a: f32, b: f32) -> f32 {
    return nf_truth(a, b, a != b);
}

// The branch of a `piecewise` whose condition is `c`, else `rest`.
fn nf_branch(c: f32, v: f32, rest: f32) -> f32 {
    if nf_undef(c) {
        return nf_nan();
    }
    return select(rest, v, c == 1.0);
}

fn nf_erf(x: f32) -> f32 {
    if nf_undef(x) {
        return x;
    }
    let a = abs(x);
    if a < 0.5 {
        let x2 = x * x;
        return 1.1283791670955126 * x
            * (1.0 + x2 * (-1.0 / 3.0 + x2 * (0.1 + x2 * (-1.0 / 42.0 + x2 * (1.0 / 216.0 - x2 / 1320.0)))));
    }
    if a > 6.0 {
        return sign(x);
    }
    // Abramowitz and Stegun 7.1.26
    let t = 1.0 / (1.0 + 0.3275911 * a);
    let poly = t * (0.254829592 + t * (-0.284496736 + t * (1.421413741 + t * (-1.453152027 + t * 1.061405429))));
    return sign(x) * (1.0 - poly * exp(-a * a));
}

fn nf_erfi(x: f32) -> f32 {
    if nf_undef(x) {
        return x;
    }
    let sqrt_pi = 1.7724538509055159;
    if abs(x) < 5.0 {
        // `2/sqrt(pi) sum x^(2n+1) / (n! (2n+1))`
        var term = x;
        var sum = x;
        var n = 0.0;
        for (var i = 0; i < 200; i++) {
            if abs(term) <= 1e-8 * abs(sum) {
                break;
            }
            n += 1.0;
            term *= x * x / n;
            sum += term / (2.0 * n + 1.0);
        }
        return 2.0 / sqrt_pi * sum;
    }
    // `e^(x^2) / (x sqrt(pi)) (1 + 1/(2x^2) + 3/(4x^4) + ...)`
    let inv = 1.0 / (2.0 * x * x);
    var term = 1.0;
    var sum = 1.0;
    for (var n = 1; n < 20; n++) {
        term *= f32(2 * n - 1) * inv;
        sum += term;
    }
    return nf_exp(x * x) / (x * sqrt_pi) * sum;
}

// `Gamma(z)` for `z >= 1/2`, by Lanczos' approximation.
fn nf_gamma_right(z0: f32) -> f32 {
    let z = z0 - 1.0;
    var a = 0.99999999999980993;
    a += 676.5203681218851 / (z + 1.0);
    a += -1259.1392167224028 / (z + 2.0);
    a += 771.32342877765313 / (z + 3.0);
    a += -176.61502916214059 / (z + 4.0);
    a += 12.507343278686905 / (z + 5.0);
    a += -0.13857109526572012 / (z + 6.0);
    a += 9.9843695780195716e-6 / (z + 7.0);
    a += 1.5056327351493116e-7 / (z + 8.0);
    let t = z + 7.5;
    return 2.5066282746310002 * nf_exp((z + 0.5) * log(t) - t) * a;
}

// `Gamma(x)`, NaN at its poles.
fn nf_gamma(x: f32) -> f32 {
    if nf_undef(x) || (x <= 0.0 && fract(x) == 0.0) || x == -nf_inf() {
        return nf_nan();
    }
    if x >= 0.5 {
        if x > 40.0 {
            return nf_inf();
        }
        return nf_gamma_right(x);
    }
    // `Gamma(x) = pi / (sin(pi x) Gamma(1 - x))`, `sin(pi x)` reduced first
    let r = x - 2.0 * floor(x * 0.5);
    let g = nf_gamma_right(1.0 - x);
    if !nf_finite(g) {
        return 0.0;
    }
    return PI / (sin(PI * r) * g);
}

fn nf_factorial(x: f32) -> f32 {
    return nf_gamma(x + 1.0);
}

// `binom(n, k)`, exact on integers.
fn nf_binomial(n: f32, k: f32) -> f32 {
    if nf_undef(n) || nf_undef(k) {
        return nf_nan();
    }
    if fract(k) == 0.0 && fract(n) == 0.0 && k >= 0.0 && k <= 1000.0 {
        if k > n && n >= 0.0 {
            return 0.0;
        }
        var res = 1.0;
        var i = 0.0;
        loop {
            if i >= k {
                break;
            }
            res *= (n - i) / (i + 1.0);
            i += 1.0;
        }
        return round(res);
    }
    return nf_gamma(n + 1.0) / (nf_gamma(k + 1.0) * nf_gamma(n - k + 1.0));
}

// `n!` for a small integer `n`.
fn nf_fact(n: u32) -> f32 {
    var res = 1.0;
    for (var i = 2u; i <= n; i++) {
        res *= f32(i);
    }
    return res;
}

// The Bernoulli number `B_(2k)`, `1 <= k <= 7`.
fn nf_bernoulli(k: u32) -> f32 {
    switch k {
        case 1u: { return 1.0 / 6.0; }
        case 2u: { return -1.0 / 30.0; }
        case 3u: { return 1.0 / 42.0; }
        case 4u: { return -1.0 / 30.0; }
        case 5u: { return 5.0 / 66.0; }
        case 6u: { return -691.0 / 2730.0; }
        default: { return 7.0 / 6.0; }
    }
}

// `psi^((m))(x)`, by the recurrence up to `x >= 10` then the asymptotic series.
fn nf_polygamma(mf: f32, x0: f32) -> f32 {
    if nf_undef(mf) || nf_undef(x0) || mf < 0.0 || fract(mf) != 0.0 || mf > 100.0 || (x0 <= 0.0 && fract(x0) == 0.0)
        || !nf_finite(x0) {
        return nf_nan();
    }
    let m = u32(mf);
    let parity = select(-1.0, 1.0, m % 2u == 0u);
    let fm = nf_fact(m);
    var x = x0;
    var shift = 0.0;
    var steps = 0;
    loop {
        if x >= 10.0 {
            break;
        }
        // `psi^((m))(x) = psi^((m))(x + 1) - (-1)^m m! / x^(m+1)`
        shift -= parity * fm / nf_powi(x, i32(m) + 1);
        x += 1.0;
        steps += 1;
        if steps > 1000 {
            return nf_nan();
        }
    }
    var series: f32;
    if m == 0u {
        series = log(x) - 0.5 / x;
    } else {
        series = nf_fact(m - 1u) / nf_powi(x, i32(m)) + fm / (2.0 * nf_powi(x, i32(m) + 1));
    }
    for (var k = 1u; k <= 7u; k++) {
        let b = nf_bernoulli(k);
        if m == 0u {
            series -= b / (2.0 * f32(k) * nf_powi(x, 2 * i32(k)));
        } else {
            series += b * nf_fact(2u * k + m - 1u) / (nf_fact(2u * k) * nf_powi(x, 2 * i32(k) + i32(m)));
        }
    }
    if m > 0u && m % 2u == 0u {
        series = -series;
    }
    return series + shift;
}

// `zeta(s)` for `s >= -2`, by Euler-Maclaurin summation.
fn nf_zeta_right(s: f32) -> f32 {
    let n = 12.0;
    var sum = 0.0;
    for (var k = 1; k < 12; k++) {
        sum += pow(f32(k), -s);
    }
    sum += pow(n, 1.0 - s) / (s - 1.0) + 0.5 * pow(n, -s);
    // `sum_k B_(2k) / (2k)! s (s+1) ... (s+2k-2) N^(-s-2k+1)`
    var rising = s;
    var factorial = 2.0;
    for (var k = 1u; k <= 7u; k++) {
        sum += nf_bernoulli(k) / factorial * rising * pow(n, -s - f32(2u * k) + 1.0);
        let kf = f32(k);
        rising *= (s + 2.0 * kf - 1.0) * (s + 2.0 * kf);
        factorial *= (2.0 * kf + 1.0) * (2.0 * kf + 2.0);
    }
    return sum;
}

fn nf_zeta(s: f32) -> f32 {
    if s == 1.0 || nf_undef(s) {
        return nf_nan();
    }
    // Unlike in f64, the functional equation loses precision near 0, from `zeta(1 - s)`
    if s >= -2.0 {
        if s > 30.0 {
            return 1.0;
        }
        return nf_zeta_right(s);
    }
    if s < 0.0 && fract(s * 0.5) == 0.0 {
        return 0.0;
    }
    // `zeta(s) = 2^s pi^(s-1) sin(pi s / 2) Gamma(1 - s) zeta(1 - s)`
    let r = s - 4.0 * floor(s * 0.25);
    return pow(2.0, s) * pow(PI, s - 1.0) * sin(PI * r * 0.5) * nf_gamma(1.0 - s) * nf_zeta_right(1.0 - s);
}

// The principal branch `W_0(x)` of the Lambert W function, by Halley's iteration.
fn nf_lambertw(x: f32) -> f32 {
    let branch = -0.36787944117144233;
    if nf_undef(x) || x < branch {
        return nf_nan();
    }
    if !nf_finite(x) {
        return x;
    }
    var w: f32;
    if x < 1.0 {
        let p = sqrt(max(2.0 * (2.718281828459045 * x + 1.0), 0.0));
        w = -1.0 + p - p * p / 3.0;
    } else {
        let l = log(1.0 + x);
        w = l - log(max(l, 1.0)) * 0.5;
    }
    for (var i = 0; i < 30; i++) {
        let e = exp(w);
        let f = w * e - x;
        let denominator = e * (w + 1.0) - (w + 2.0) * f / (2.0 * w + 2.0);
        if denominator == 0.0 || !nf_finite(denominator) {
            break;
        }
        let next = w - f / denominator;
        if abs(next - w) <= 1e-7 * (1.0 + abs(next)) {
            return next;
        }
        w = next;
    }
    return w;
}
