//! Whole series `series(f, x, a, oo)` checked against the function: inside the disk of convergence (where two
//! long partial sums agree), the partial sums of the general terms converge to `f`.

use crate::common::{
    harness::{Verdict, assert_pass, case_rng, check_all, fuzz},
    numeric::{Domain, close, decimal, eval, number, split_top, symbols},
    rng::Rng,
};
use formalith::parser::environment::Environment;
use std::time::Duration;

/// Terms of each infinite sum which are computed.
const TERMS: i64 = 90;
/// Partial sums (numbers of terms) which must agree for a point to be in the disk of convergence: consecutive
/// ones, so that oscillating sums are rejected, and a longer one.
const LENGTHS: [usize; 3] = [60, 61, 91];

/// An infinite sum `sum(t, k, a, oo)` of an output.
struct HeldSum {
    term: String,
    k: String,
    start: String,
}

/// `output` with its infinite sums replaced by the symbols `chk_s0`, `chk_s1`..., and these sums.
fn split_sums(output: &str) -> Option<(String, Vec<HeldSum>)> {
    let mut res = String::new();
    let mut sums = vec![];
    let mut rest = output;
    while let Some(start) = rest.find("sum(") {
        res.push_str(&rest[..start]);
        let after = &rest[start + 4..];
        // The matching parenthesis
        let mut depth = 1;
        let end = after.char_indices().find_map(|(i, c)| {
            match c {
                '(' => depth += 1,
                ')' => depth -= 1,
                _ => {}
            }
            (depth == 0).then_some(i)
        })?;
        let args = split_top(&after[..end], ',');
        if args.len() != 4 {
            return None;
        }
        if args[3] == "oo" {
            res.push_str(&format!("chk_s{}", sums.len()));
            sums.push(HeldSum {
                term: args[0].clone(),
                k: args[1].clone(),
                start: args[2].clone(),
            });
        } else {
            res.push_str(&format!("sum({})", args.join(", ")));
        }
        rest = &after[end + 1..];
    }
    res.push_str(rest);
    Some((res, sums))
}

/// `output` with each `rootof(p, k)` written `rootof(p, chk_r, k)`, `p` being in `chk_r` instead of `x`.
fn rename_rootof_variable(output: &str) -> String {
    let mut res = String::new();
    let mut rest = output;
    while let Some(start) = rest.find("rootof(") {
        res.push_str(&rest[..start]);
        let after = &rest[start + 7..];
        let mut depth = 1;
        let Some(end) = after.char_indices().find_map(|(i, c)| {
            match c {
                '(' => depth += 1,
                ')' => depth -= 1,
                _ => {}
            }
            (depth == 0).then_some(i)
        }) else {
            return output.to_owned();
        };
        let args = split_top(&after[..end], ',');
        match args.as_slice() {
            [p, k] => res.push_str(&format!("rootof({}, chk_r, {k})", p.replace('x', "chk_r"))),
            _ => res.push_str(&format!("rootof({})", args.join(", "))),
        }
        rest = &after[end + 1..];
    }
    res.push_str(rest);
    res
}

/// The indices of every sum of `output`, nested ones included (like the convolutions of products of series).
fn sum_indices(output: &str) -> Vec<String> {
    output
        .match_indices("sum(")
        .filter_map(|(start, _)| {
            let after = &output[start + 4..];
            let mut depth = 1;
            let end = after.char_indices().find_map(|(i, c)| {
                match c {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                (depth == 0).then_some(i)
            })?;
            split_top(&after[..end], ',').get(1).cloned()
        })
        .collect()
}

/// The partial sums of `sum` with [`LENGTHS`] terms at the point of `env`, `None` if a term can't be evaluated.
fn partial_sums(env: &Environment, sum: &HeldSum) -> Option<Vec<f64>> {
    let start = number(env, &sum.start)?.round() as i64;
    let mut partial = vec![];
    let mut total = 0.;
    for (i, j) in (start..=start + TERMS).enumerate() {
        if LENGTHS.contains(&i) {
            partial.push(total);
        }
        let mut env = env.clone();
        eval(&mut env, &format!("{} := {j}", sum.k)).ok()?;
        total += number(&env, &sum.term)?;
    }
    Some(partial)
}

/// Check the whole series of `input`: `f; a`, or `f; a; side` for a one-sided series.
fn whole_series(input: &str) -> Verdict {
    let parts: Vec<_> = input.split(';').map(str::trim).collect();
    let (f, a) = (parts[0], parts[1]);
    let side = parts.get(2).map_or_else(String::new, |s| format!(", {s}"));
    let output = match eval(
        &mut Environment::new(),
        &format!("series({f}, x, {a}, oo{side})"),
    ) {
        Ok(output) => output,
        Err(e) => return Verdict::Skip(e),
    };
    verify(input, &output)
}

/// Check that `output` is the whole series of `input`.
fn verify(input: &str, output: &str) -> Verdict {
    let parts: Vec<_> = input.split(';').map(str::trim).collect();
    let (f, a) = (parts[0], parts[1]);
    if output.contains("series(") {
        return Verdict::Skip(format!("unevaluated: {output}"));
    }
    if !output.contains("sum(") {
        return Verdict::Skip(format!("no sum: {output}"));
    }
    // `rootof(p, k)` is printed with `p` in `x`, which gets values here
    let output = &rename_rootof_variable(output);
    let Some((rest, sums)) = split_sums(output) else {
        return Verdict::Wrong(format!("can't read the sums of `{output}`"));
    };
    let mut rng = case_rng(input);
    // Parameters get random values
    let mut env = Environment::new();
    let indices = sum_indices(output);
    for p in symbols(&format!("{f} + {output}")) {
        let index = indices.contains(&p) || p == "chk_r";
        if p != "x" && !index {
            let v = Domain::Range(0.3, 2.5).sample(&mut rng);
            if eval(&mut env, &format!("{p} := {v}")).is_err() {
                return Verdict::Skip(format!("can't define `{p}`"));
            }
        }
    }
    let points: Vec<String> = if a == "oo" {
        ["2", "4", "8", "-4"].map(str::to_owned).to_vec()
    } else if a == "-oo" {
        ["-2", "-4", "-8", "4"].map(str::to_owned).to_vec()
    } else {
        ["1/2", "-1/2", "1/4", "-1/4", "1/8", "-1/8"]
            .map(|t| format!("({a}) + ({t})"))
            .to_vec()
    };
    let mut checked = 0;
    'points: for point in points {
        let mut env = env.clone();
        if eval(&mut env, &format!("x := {point}")).is_err() {
            continue;
        }
        let Some(value) = number(&env, f) else {
            continue;
        };
        // Each sum by its partial sums, which must agree
        let mut with_sums = env.clone();
        for (i, sum) in sums.iter().enumerate() {
            let Some(partial) = partial_sums(&env, sum) else {
                continue 'points;
            };
            let last = partial[partial.len() - 1];
            if partial.iter().any(|s| !close(*s, last, 1e-12)) {
                // Outside of the disk of convergence, or converging too slowly
                continue 'points;
            }
            if eval(&mut with_sums, &format!("chk_s{i} := {}", decimal(last))).is_err() {
                continue 'points;
            }
        }
        let Some(series) = number(&with_sums, &rest) else {
            continue;
        };
        if !close(series, value, 1e-9) {
            return Verdict::Wrong(format!(
                "at x = {point}, the series is {series} but f = {value}: `{output}`"
            ));
        }
        checked += 1;
    }
    if checked > 0 {
        Verdict::Pass
    } else {
        Verdict::Skip(format!("no point of convergence for `{output}`"))
    }
}

#[test]
fn oracle_detects_wrong_terms() {
    let wrong = |input: &str, output: &str| matches!(verify(input, output), Verdict::Wrong(_));
    assert!(wrong("exp(x); 0", "sum((x^k)*((k+1)!^-1), k, 0, oo)"));
    // Right up to `{$x^20$}`
    assert!(wrong(
        "1/(1 - x); 0",
        "sum(x^k, k, 0, 19) + sum(2*x^k, k, 20, oo)"
    ));
    assert!(matches!(
        verify("exp(x); 0", "sum((x^k)*(k!^-1), k, 0, oo)"),
        Verdict::Pass
    ));
}

#[test]
fn whole_series_examples() {
    check_all(
        "whole series",
        &[
            "exp(x); 0",
            "sin(x); 0",
            "cos(x); 0",
            "atan(x); 0",
            "asin(x); 0",
            "ln(1 + x); 0",
            "(1 + x)^a; 0",
            "1/(1 + x^2); 0",
            "1/((1 - x)*(1 - 2*x)); 0",
            "exp(x); 1",
            "(exp(x) - 1)/x; 0",
            "1/(x - 1); oo",
            "exp(x) + sin(x); 0",
            "1/(1 - x - x^2); 0",
            "erf(x); 0",
            "sinh(2*x); 0",
            "x*exp(-x^2); 0",
            "1/(1 - x)^3; 0",
            "cos(x)^2; 0",
            "sqrt(1 + x); 0",
            "asinh(x); 0",
            "exp(x)*sin(x); 0",
            "Si(x); 0",
            "sqrt(1 + sqrt(1 + x)); 0",
            "1/sqrt(1 + sqrt(1 + x)); 0",
            "sqrt(1 + sqrt(x)); 0; 1",
            "sqrt(x + x^2); 0; 1",
            "sqrt(x)*exp(x); 0; 1",
            "tan(x); 0",
            "1/cos(x); 0",
            "x/(exp(x) - 1); 0",
            "cot(x); 0",
            "tanh(x); 0",
            "1/sinh(2*x); 0",
            "x^2/sin(x); 0",
            "1/(1 - x + 2*x^2); 0",
            "1/((1 - 2*x)*(1 + x + 2*x^2)); 0",
            "(x + 3)/(x^2 + x + 3); oo",
            "tan(x)^2; 0",
            "tan(x)^3; 0",
            "tanh(2*x)^2; 0",
            "1/cos(x)^2; 0",
            "1/sin(x)^2; 0",
            "1/sinh(x)^4; 0",
            "x*tan(x)^2; 0",
            "tan(x)/(1 + x); 0",
            "exp(x)*tan(x); 0",
            "(1 + x^2)*tan(x); 0",
            "tan(x)/(1 - 2*x); 0",
            "1/(1 - x - x^2)^2; 0",
            "1/(1 - 2*x^2)^2; 0",
            "1/((1 - x)^2*(1 + x^2)); 0",
            "1/(1 - x + 2*x^2)^2; 0",
            "(1 + x)/(1 - 3*x^2)^3; 0",
            "exp(x)*cosh(2*x); 0",
            "cosh(x)*cosh(2*x); 0",
            "sinh(x)*exp(2*x); 0",
            "exp(x)*sin(x)*cosh(x); 0",
            "x*exp(-x)*cosh(3*x); 0",
            "exp(2*x)*cos(x)^2; 0",
        ],
        whole_series,
    );
}

#[test]
fn whole_series_of_kernels_at_regular_points() {
    // Slow to check: the terms have several polygammas which cancel
    check_all(
        "kernels at regular points",
        &[
            "tan(x); 1",
            "1/tan(x); 1",
            // Through the partial fractions of `{$1/sin$}`
            "1/cos(x); 2",
            "x*tan(2*x); 1/2",
        ],
        whole_series,
    );
}

/// An atom of the holonomic closure rules.
fn atom(rng: &mut Rng) -> String {
    let c = rng.nonzero(3);
    let q = rng.range(1, 3);
    match rng.below(12) {
        0 => format!("exp({c}*x/{q})"),
        1 => format!("sin({c}*x)"),
        2 => format!("cos({c}*x/{q})"),
        3 => format!("sinh({c}*x)"),
        4 => format!("atan({c}*x/{q})"),
        5 => format!("ln(1 + x/{})", rng.range(2, 4)),
        6 => format!("1/(1 + {c}*x/{})", rng.range(2, 4)),
        7 => format!("(1 + x/{})^({c}/{q})", rng.range(2, 4)),
        8 => format!("erf({c}*x)"),
        9 => format!("asin(x/{})", rng.range(2, 4)),
        10 => format!("1/(({}  - x)*({} + x))", rng.range(2, 4), rng.range(2, 4)),
        _ => format!("x^{}", rng.range(1, 3)),
    }
}

/// A random function with a whole series at 0: atoms, their sums and products.
fn function(rng: &mut Rng) -> String {
    match rng.below(4) {
        0 => atom(rng),
        1 => format!("{} + {}*{}", atom(rng), rng.nonzero(3), atom(rng)),
        2 => format!("({})*({})", atom(rng), atom(rng)),
        _ => format!("{}*({})", rng.nonzero(4), atom(rng)),
    }
}

/// A random rational function at another point or at infinity.
fn rational(rng: &mut Rng) -> String {
    let (b, c) = (rng.range(-3, 3), rng.range(2, 5));
    match rng.below(3) {
        0 => format!("1/(x - {b}); {c}"),
        1 => format!("x/((x - {b})*(x + {c})); oo"),
        _ => format!("1/(x^2 + {c}); oo"),
    }
}

#[test]
#[ignore = "fuzz: random whole series at 0, run with --ignored"]
fn fuzz_whole_series() {
    fuzz(
        "fuzz whole series",
        80,
        |rng| format!("{}; 0", function(rng)),
        whole_series,
    );
}

#[test]
#[ignore = "fuzz: random rational functions at other points, run with --ignored"]
fn fuzz_rational_series() {
    fuzz("fuzz rational series", 40, rational, whole_series);
}

fn regression(input: &str) {
    assert_pass(input, Duration::from_secs(60), whole_series);
}

#[test]
fn bug_sum_without_common_recurrence_hangs() {
    // Recurrences were guessed over `{$QQ(sqrt(pi))$}` for every period and degree before splitting the sum
    regression("erf(x) + exp(x); 0");
    regression("exp(-x/3) + erf(3*x); 0");
}

#[test]
fn bug_rational_terms_and_polynomial_factors() {
    regression("-sin(x) + 1/((4 - x)*(3 + x)); 0");
    regression("(x/2 + 1)*atan(2*x); 0");
    regression("(x/3 + 1)*exp(-x/3); 0");
}
