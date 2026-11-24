//! `approx` checked against an independent evaluation and against itself: at rational points, `approx(f, 40)`
//! agrees with the f64 evaluation of `Numeric` (libm and its own special functions), and `approx(f, 15)` is
//! `approx(f, 40)` rounded to 15 significant digits.
mod common;

use common::{
    harness::{Verdict, assert_pass, case_rng, check_all, fuzz},
    numeric::{Domain, eval},
    rng::Rng,
};
use formalith::{
    field::real::{R, numeric::Numeric},
    parser::environment::Environment,
    symbol, try_parse,
};
use malachite::{
    Integer, Rational,
    base::{
        num::{
            arithmetic::traits::{Abs, Pow},
            conversion::traits::RoundingFrom,
        },
        rounding_modes::RoundingMode,
    },
};
use std::{str::FromStr, time::Duration};

/// Points where each function is evaluated.
const POINTS: usize = 5;
/// Relative (or absolute, near 0) tolerance between `approx` and the f64 evaluation.
const F64_TOLERANCE: f64 = 1e-9;

/// A decimal printed by `approx`, like `-1.92874984796392e-22`, as an exact rational.
fn parse_decimal(text: &str) -> Option<Rational> {
    let (mantissa, exponent) = match text.split_once('e') {
        Some((m, e)) => (m, e.parse::<i64>().ok()?),
        None => (text, 0),
    };
    let (negative, mantissa) = match mantissa.strip_prefix('-') {
        Some(m) => (true, m),
        None => (false, mantissa),
    };
    let (int, frac) = mantissa.split_once('.').unwrap_or((mantissa, ""));
    let digits = Integer::from_str(&format!("{int}{frac}")).ok()?;
    let scale = exponent - i64::try_from(frac.len()).ok()?;
    let value = Rational::from(digits) * Rational::from(10).pow(scale);
    Some(if negative { -value } else { value })
}

/// The nearest float.
fn to_f64(value: &Rational) -> f64 {
    f64::rounding_from(value, RoundingMode::Nearest).0
}

/// `approx(expr, digits)` with `x := point`, as a rational, `None` when it isn't a number.
fn approx_at(f: &str, point: &str, digits: u64) -> Option<Rational> {
    let mut env = Environment::new();
    eval(&mut env, &format!("x := {point}")).ok()?;
    let output = common::guard::no_panic(|| eval(&mut env, &format!("approx({f}, {digits})")))?;
    parse_decimal(output.ok()?.trim())
}

/// Check `approx` on `f`, a function of `x`, at points of `[0.2, 3]` (`f`; `lo`; `hi` gives another interval).
fn approx(input: &str) -> Verdict {
    let parts: Vec<_> = input.split(';').map(str::trim).collect();
    let f = parts[0];
    let domain = match (parts.get(1), parts.get(2)) {
        (Some(lo), Some(hi)) => Domain::Range(lo.parse().unwrap(), hi.parse().unwrap()),
        _ => Domain::Range(0.2, 3.0),
    };
    let Some(term) = common::guard::no_panic(|| try_parse!(f, R).ok()).flatten() else {
        return Verdict::Skip(format!("can't parse `{f}`"));
    };
    let numeric = Numeric::compile(&term, &[symbol!("x")]);
    if let Some(name) = numeric.unsupported() {
        return Verdict::Skip(format!("`{name}` has no f64 form in `{f}`"));
    }
    let mut rng = case_rng(input);
    let mut checked = 0;
    for _ in 0..POINTS {
        let point = domain.sample(&mut rng);
        let (Some(precise), Some(rounded)) = (approx_at(f, &point, 40), approx_at(f, &point, 15))
        else {
            continue;
        };
        // 15 significant digits
        let error = (&precise - &rounded).abs();
        if error > (&precise).abs() / Rational::from(10).pow(14i64) {
            return Verdict::Wrong(format!(
                "at x = {point}, approx(f, 15) = {} but approx(f, 40) = {}",
                to_f64(&rounded),
                to_f64(&precise)
            ));
        }
        let Some(x0) = rational_point(&point) else {
            continue;
        };
        let fast = numeric.eval(&[to_f64(&x0)]);
        let exact = to_f64(&precise);
        if !fast.is_finite() {
            continue;
        }
        if (fast - exact).abs() > F64_TOLERANCE * exact.abs().max(1.0) {
            return Verdict::Wrong(format!(
                "at x = {point}, approx(f, 40) = {exact} but the f64 evaluation gives {fast}"
            ));
        }
        checked += 1;
    }
    if checked >= 2 {
        Verdict::Pass
    } else {
        Verdict::Skip(format!("only {checked} points evaluated"))
    }
}

/// The rational `p/q` of a sampled point.
fn rational_point(point: &str) -> Option<Rational> {
    let (p, q) = point.split_once('/')?;
    Some(Rational::from(Integer::from_str(p).ok()?) / Rational::from(Integer::from_str(q).ok()?))
}

#[test]
fn decimals() {
    let r = |p: i64, q: i64| Rational::from(p) / Rational::from(q);
    assert_eq!(parse_decimal("1.5"), Some(r(3, 2)));
    assert_eq!(parse_decimal("-2.0"), Some(r(-2, 1)));
    assert_eq!(parse_decimal("1.0e20"), Some(Rational::from(10).pow(20i64)));
    assert_eq!(parse_decimal("1.25e-2"), Some(r(1, 80)));
    assert_eq!(parse_decimal("ln(-2)"), None);
}

#[test]
fn elementary_functions() {
    check_all(
        "approx elementary",
        &[
            "exp(x)",
            "ln(x)",
            "sin(x) + cos(x)",
            "tan(x/2)",
            "asin(x/4) + acos(x/4)",
            "atan(x)",
            "sinh(x) - cosh(x)",
            "tanh(x)",
            "asinh(x)",
            "acosh(x + 1)",
            "atanh(x/4)",
            "x^x",
            "sqrt(x^2 + 1)",
            "(x + 1)^(1/3)",
            "exp(sin(x))/(1 + x^2)",
            "abs(x - 1) + floor(2*x)",
            "x^pi",
            "pi^x",
        ],
        approx,
    );
}

#[test]
fn special_functions() {
    check_all(
        "approx special",
        &[
            "gamma(x)",
            "gamma(x + 1/3)",
            "factorial(x)",
            "polygamma(0, x)",
            "polygamma(1, x + 1)",
            "polygamma(3, x)",
            "zeta(x + 1)",
            "zeta(x + 2)",
            "lambertw(x)",
            "lambertw(-x/10)",
            "lambertw(-x/10, -1)",
            "erf(x)",
            "erfi(x)",
            "erf(x) + erf(-x/2)",
            "Si(x)",
            "Si(10*x)",
            "Ci(x)",
            "Ei(x)",
            "Ei(-x)",
            "binomial(x + 2, 2)",
            "beta(x, 2)",
        ],
        approx,
    );
}

/// Functions of one argument of random expressions.
const UNARY: [&str; 22] = [
    "exp", "ln", "sin", "cos", "tan", "atan", "sinh", "cosh", "tanh", "asinh", "sqrt", "erf",
    "erfi", "gamma", "lambertw", "Si", "Ci", "Ei", "zeta", "abs", "asin", "acosh",
];

/// A random function of `x` with depth at most `depth`.
fn function(rng: &mut Rng, depth: usize) -> String {
    if depth == 0 || rng.chance(0.2) {
        return if rng.chance(0.6) {
            let (a, b) = (rng.nonzero(3), rng.range(-2, 2));
            format!("({a}*x + {b})")
        } else {
            format!("{}/{}", rng.nonzero(5), rng.range(1, 4))
        };
    }
    match rng.below(7) {
        0 => format!(
            "({} + {})",
            function(rng, depth - 1),
            function(rng, depth - 1)
        ),
        1 => format!(
            "({} * {})",
            function(rng, depth - 1),
            function(rng, depth - 1)
        ),
        2 => format!(
            "({} / {})",
            function(rng, depth - 1),
            function(rng, depth - 1)
        ),
        3 => format!("({})^{}", function(rng, depth - 1), rng.range(2, 3)),
        4 => format!(
            "polygamma({}, {})",
            rng.range(0, 2),
            function(rng, depth - 1)
        ),
        _ => format!("{}({})", rng.pick(&UNARY), function(rng, depth - 1)),
    }
}

#[test]
#[ignore = "fuzz: random functions, run with --ignored"]
fn fuzz_approx() {
    fuzz("fuzz approx", 150, |rng| function(rng, 3), approx);
}

fn regression(input: &str) {
    assert_pass(input, Duration::from_secs(60), approx);
}

#[test]
fn bug_ci_near_the_asymptotic_switch() {
    // The f64 form of `{$"Ci"$}` used its asymptotic series from 16, accurate to about `{$e^(-x)$}`
    regression("x + Ci((3*x + 1)*(x + 1)); 1.5; 2");
}

#[test]
fn bug_polygamma_of_large_negative_approximations() {
    // The terms of the shift of `{$zeta(s, x)$}` were summed exactly, with growing denominators when `x` is an
    // approximation
    regression("polygamma(1, polygamma(2, 5/3)*cosh(3*x + 1)); 2.4; 2.6");
    regression("polygamma(0, -x*1000)");
}
