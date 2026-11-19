//! Integration checked against its definition: the derivative of an antiderivative is the integrand, and definite
//! integrals agree with a numerical quadrature.
mod common;

use common::{
    harness::{Verdict, assert_pass, case_rng, check_all, fuzz},
    numeric::{Domain, Function, close, decimal, env_with, eval, number},
    random,
};
use std::time::Duration;

/// Points where the derivative of the antiderivative is compared to the integrand.
const POINTS: usize = 6;

/// Check that `integrate(f, x)` has derivative `f`, numerically (central differences, not `diff`).
fn antiderivative(f: &str) -> Verdict {
    let mut env = env_with(&[]);
    let antiderivative = match eval(&mut env, &format!("integrate({f}, x)")) {
        Ok(res) if !res.contains("integrate") => res,
        Ok(res) => return Verdict::Skip(format!("unevaluated: {res}")),
        Err(e) => return Verdict::Skip(e),
    };
    let (Ok(big_f), Ok(small_f)) = (
        Function::new(&env, &antiderivative, &["x"]),
        Function::new(&env, f, &["x"]),
    ) else {
        return Verdict::Skip(format!("can't define `{antiderivative}`"));
    };
    let mut rng = case_rng(f);
    let mut valid = 0;
    for _ in 0..POINTS * 2 {
        let x0 = Domain::Range(-3.0, 3.0).sample(&mut rng);
        let (Some(d), Some(v)) = (big_f.derivative_at(&x0), small_f.at(&[x0.clone()])) else {
            continue;
        };
        if !close(d, v, 1e-7) {
            return Verdict::Wrong(format!(
                "F = {antiderivative}: F'({x0}) = {d} but f({x0}) = {v}"
            ));
        }
        valid += 1;
        if valid == POINTS {
            break;
        }
    }
    if valid >= 3 {
        Verdict::Pass
    } else {
        Verdict::Skip(format!(
            "only {valid} valid points for F = {antiderivative}"
        ))
    }
}

/// Check `integrate(f, x, a, b)` against Gauss-Legendre quadrature. `input` is `f; a; b`.
fn definite(input: &str) -> Verdict {
    let [f, a, b]: [&str; 3] = input
        .split(';')
        .map(str::trim)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let mut env = env_with(&[]);
    let exact = match eval(&mut env, &format!("integrate({f}, x, {a}, {b})")) {
        Ok(res) if !res.contains("integrate") => res,
        Ok(res) => return Verdict::Skip(format!("unevaluated: {res}")),
        Err(e) => return Verdict::Skip(e),
    };
    let (Some(lo), Some(hi)) = (number(&env, a), number(&env, b)) else {
        return Verdict::Skip("bounds".to_owned());
    };
    let Some(value) = number(&env, &exact) else {
        return Verdict::Skip(format!("result `{exact}` isn't a number"));
    };
    let Ok(integrand) = Function::new(&env, f, &["x"]) else {
        return Verdict::Skip("definition".to_owned());
    };
    let Some(quad) = integrand.quadrature(lo, hi, 8) else {
        return Verdict::Skip(format!("integrand doesn't evaluate on [{a}, {b}]"));
    };
    // Gauss-Legendre is exact enough for smooth integrands; check with a coarser rule too
    let coarse = integrand.quadrature(lo, hi, 4).unwrap_or(quad);
    if !close(quad, coarse, 1e-8) {
        return Verdict::Skip(format!("quadrature didn't converge ({quad} vs {coarse})"));
    }
    if close(value, quad, 1e-7) {
        Verdict::Pass
    } else {
        Verdict::Wrong(format!(
            "exact `{exact}` = {value} but quadrature gives {quad}"
        ))
    }
}

#[test]
fn antiderivatives() {
    check_all(
        "antiderivatives",
        &[
            "x^3 - 2*x + 1",
            "exp(2*x) * sin(3*x)",
            "x * cos(x)",
            "1/(x^2 + 1)",
            "1/(x^2 - 4)",
            "(x + 1)/((x - 2)*(x^2 + 2*x + 5))",
            "x^2 * exp(-x)",
            "ln(x^2 + 1)",
            "atan(x)",
            "sin(x)^3 * cos(x)^2",
            "sqrt(4 - x^2)",
            "x / sqrt(x^2 + 1)",
            "exp(-x^2)",
            "tan(x)",
            "x * exp(x^2)",
            "1/(exp(x) + 1)",
            "sinh(2*x) * x",
        ],
        antiderivative,
    );
}

#[test]
fn definite_integrals() {
    check_all(
        "definite integrals",
        &[
            "x^2 * sin(x); 0; pi",
            "1/(1 + x^2); -1; 2",
            "exp(-x) * x^3; 0; 3",
            "ln(x); 1; 4",
            "x * exp(-x^2); -1; 2",
            "1/(x + 3); -2; 5",
            "x / (x^2 + 2*x + 2); 0; 2",
            "abs(x - 1); -1; 3",
        ],
        definite,
    );
}

#[test]
#[ignore = "fuzz: random integrands, run with --ignored"]
fn fuzz_antiderivatives() {
    fuzz(
        "fuzz antiderivatives",
        60,
        random::integrand,
        antiderivative,
    );
}

#[test]
#[ignore = "fuzz: random definite integrals, run with --ignored"]
fn fuzz_definite_integrals() {
    fuzz(
        "fuzz definite integrals",
        40,
        |rng| {
            let f = random::integrand(rng);
            let a = rng.range(-2, 1);
            let b = a + rng.range(1, 3);
            format!("{f}; {}; {}", decimal(a as f64), decimal(b as f64))
        },
        definite,
    );
}

#[test]
#[ignore = "fuzz: random expressions, run with --ignored"]
fn fuzz_antiderivatives_of_random_expressions() {
    fuzz(
        "fuzz random antiderivatives",
        60,
        |rng| random::expr(rng, &["x"], 3),
        antiderivative,
    );
}

fn regression(input: &str, check: fn(&str) -> Verdict) {
    assert_pass(input, Duration::from_secs(60), check);
}

#[test]
#[ignore = "bug: integrate(sin(1/ln(x)), x) is 0"]
fn bug_integrate_sin_of_reciprocal_ln() {
    // Also `cos(1/ln(x))`; the definite integral on `[2, 3]` is 0 too, its integrand being positive there
    regression("sin(1/ln(x)); 2; 3", definite);
    regression("cos(1/ln(x))", antiderivative);
}

#[test]
fn bug_integrate_sqrt_over_linear_panics() {
    regression("sqrt(x)/(2*x - 1)", antiderivative);
}

#[test]
#[ignore = "bug: integrate(sqrt(2*x + 1)*sqrt(3*x + 1), x) hangs"]
fn bug_integrate_product_of_square_roots_hangs() {
    regression("sqrt(2*x + 1)*sqrt(3*x + 1)", antiderivative);
}
