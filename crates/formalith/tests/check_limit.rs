//! Limits checked numerically: `f` evaluated close to the point (or at large `x` for `oo`) approaches the limit.
//! Cases are kept well-conditioned (no essential singularities, limits reached at a polynomial rate).
mod common;

use common::{
    harness::{Verdict, check_all, fuzz},
    numeric::{Function, env_with, eval, number},
    random,
    rng::Rng,
};

/// Points approaching `a` from `side` (`1` right, `-1` left), as expressions.
fn approach(a: &str, side: i64) -> [String; 2] {
    match a {
        "oo" => ["10^3".to_owned(), "10^5".to_owned()],
        "-oo" => ["-10^3".to_owned(), "-10^5".to_owned()],
        _ => [4, 8].map(|e| format!("({a}) + {side}/10^{e}")),
    }
}

/// `f` at `x`: exact near finite points (approximate arithmetic loses the cancellations of `0/0` forms), from an
/// approximation at infinity (exact powers like `(1 + 10^-5)^(10^5)` are huge).
fn eval_point(f: &Function, a: &str, x: &str) -> Option<f64> {
    if a.ends_with("oo") {
        f.at_approx(&[x.to_owned()], 60)
    } else {
        f.at(&[x.to_owned()])
    }
}

/// Check `lim(f, x, a[, side])` for `input` = `f; a` or `f; a; side`.
fn limit(input: &str) -> Verdict {
    let parts: Vec<_> = input.split(';').map(str::trim).collect();
    let (f, a) = (parts[0], parts[1]);
    let side: Option<i64> = parts.get(2).map(|s| s.parse().unwrap());
    let mut env = env_with(&[]);
    let call = side.map_or_else(
        || format!("lim({f}, x, {a})"),
        |s| format!("lim({f}, x, {a}, {s})"),
    );
    let result = match eval(&mut env, &call) {
        Ok(res) if !res.contains("lim(") => res,
        Ok(res) => return Verdict::Skip(format!("unevaluated: {res}")),
        Err(e) => return Verdict::Skip(e),
    };
    let Ok(function) = Function::new(&env, f, &["x"]) else {
        return Verdict::Skip("definition".to_owned());
    };
    let sides = match (side, a) {
        (Some(s), _) => vec![s],
        (None, "oo" | "-oo") => vec![1],
        (None, _) => vec![1, -1],
    };
    let mut checked = false;
    for s in sides {
        let [far, near] = approach(a, s);
        let (Some(v_far), Some(v_near)) = (
            eval_point(&function, a, &far),
            eval_point(&function, a, &near),
        ) else {
            continue;
        };
        checked = true;
        match result.as_str() {
            "undefined" => {}
            "oo" | "-oo" => {
                let sign = if result == "oo" { 1.0 } else { -1.0 };
                if !(v_near * sign > 1e2 && v_near * sign > v_far * sign) {
                    return Verdict::Wrong(format!(
                        "lim = {result} but f({near}) = {v_near}, f({far}) = {v_far}"
                    ));
                }
            }
            _ => {
                let Some(l) = number(&env, &result) else {
                    return Verdict::Skip(format!("`{result}` isn't a number"));
                };
                let (e_far, e_near) = ((v_far - l).abs(), (v_near - l).abs());
                if e_near > 1e-3 * l.abs().max(1.0) && e_near >= e_far / 5.0 {
                    return Verdict::Wrong(format!(
                        "lim = {result} = {l} but f({far}) = {v_far}, f({near}) = {v_near}"
                    ));
                }
            }
        }
    }
    if checked {
        Verdict::Pass
    } else {
        Verdict::Skip("f doesn't evaluate near the point".to_owned())
    }
}

#[test]
fn limits() {
    check_all(
        "limits",
        &[
            "sin(x)/x; 0",
            "(1 - cos(x))/x^2; 0",
            "(exp(x) - 1 - x)/x^2; 0",
            "(1 + 1/x)^x; oo",
            "(1 + 3/x)^(2*x); oo",
            "ln(x)/sqrt(x); oo",
            "sqrt(x^2 + 3*x) - x; oo",
            "(x^2 - 4)/(x - 2); 2",
            "(x^3 - 1)/(x^2 - 1); 1",
            "1/x; 0; 1",
            "1/x; 0; -1",
            "x*ln(x); 0; 1",
            "atan(x); -oo",
            "x^3*exp(-x/50); oo",
            "(2*x^3 + x)/(5*x^3 - 7); oo",
            "(sqrt(1 + x) - 1)/x; 0",
            "tan(3*x)/sin(2*x); 0",
            "(exp(2*x) - 1)/ln(1 + x); 0",
            "x*sin(1/x); oo",
            "(x - sin(x))/x^3; 0",
            "erf(x); oo",
            "gamma(x)*x; 0; 1",
            "abs(x)/x; 0; -1",
            "floor(x); 2; -1",
        ],
        limit,
    );
}

/// Limits of oscillating functions, through the bounds of terms with angles (`limit/bounds.rs`).
#[test]
fn oscillating_limits() {
    check_all(
        "oscillating limits",
        &[
            "exp(sin(x))/x; oo",
            "sin(x)/(x*(2 + cos(x))); oo",
            "1/(2 + sin(x)*cos(x)); oo",
            "1/(x*(2 + sin(x))^2); oo",
            "ln(2 + sin(x))/x; oo",
            "sqrt(2 + sin(x))/x; oo",
            "1/(x*(2 + abs(sin(x)))); oo",
            "(3 + sin(x))^(-2)/x; oo",
            "x/(2 + sin(x)); oo",
            "1/(x*(1 + exp(sin(x)))); oo",
            "sin(x)^3/x; oo",
            "x*(2 + sin(x))^(1/3); oo",
        ],
        limit,
    );
}

/// Roots of odd order of negative values are real: `{$(-x)^(1/3) = -x^(1/3)$}` at `{$-oo$}` and on the left of 0.
#[test]
fn odd_roots() {
    check_all(
        "odd roots",
        &[
            "x^(5/3); -oo",
            "(x - 4)*x^(1/3); -oo",
            "x^(2/3); -oo",
            "x^(1/3); 0; -1",
            "x^(1/3)/x; 0; -1",
            "(x^3 + x)^(1/3) - x; -oo",
        ],
        limit,
    );
}

/// A random limit with a removable or known singularity.
fn limit_case(rng: &mut Rng) -> String {
    let a = rng.range(-2, 2);
    let c = random::constant(rng);
    match rng.below(6) {
        // Difference quotient: the derivative of `g` at `a`
        0 => {
            let g = random::expr(rng, &["x"], 2);
            let at = |x: &str| g.replace('x', &format!("({x})"));
            format!("({} - {})/(x - {a}); {a}", at("x"), at(&a.to_string()))
        }
        // Common factor
        1 => {
            let p = random::univariate(rng, "x", 2, 3);
            let q = random::univariate(rng, "x", 2, 3);
            format!("((x - {a})*{p})/((x - {a})*{q}); {a}")
        }
        // Rational function at infinity
        2 => {
            let (dp, dq) = (rng.range(0, 3) as usize, rng.range(0, 3) as usize);
            let p = random::univariate(rng, "x", dp, 4);
            let q = random::univariate(rng, "x", dq, 4);
            format!("{p}/{q}; {}", rng.pick(&["oo", "-oo"]))
        }
        // Exponential and logarithmic growth
        3 => format!(
            "x^{}*exp({}*x)*ln(x)^{}; oo",
            rng.range(-2, 3),
            rng.pick(&["-1", "-1/2", "1/3"]),
            rng.range(0, 2)
        ),
        // Classic `0/0` forms
        4 => {
            let f = rng.pick(&["sin", "tan", "atan", "sinh"]);
            let g = rng.pick(&["exp", "cosh"]);
            format!(
                "({f}({c}*x) - {c}*x)/({g}(x) - 1 - x)^{}; 0",
                rng.range(1, 2)
            )
        }
        // Continuous point: the limit is the value
        _ => format!("{}; {a}/3", random::expr(rng, &["x"], 3)),
    }
}

#[test]
#[ignore = "fuzz: random limits, run with --ignored"]
fn fuzz_limits() {
    fuzz("fuzz limits", 80, limit_case, limit);
}
