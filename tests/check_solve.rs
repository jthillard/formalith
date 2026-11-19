//! Equation solving checked against its definition: every alternative of the solution, substituted in every
//! equation, satisfies it (at random values of the free unknowns, parameters and integers `k`), and a known
//! solution of a generated system is among the alternatives.
mod common;

use common::{
    harness::{Verdict, assert_pass, case_rng, check_all, fuzz},
    numeric::{close, eval_in, number, parse_number, split_top, symbols},
    random,
    rng::Rng,
};
use formalith::{parser::environment::Environment, repl::SetChoice};
use std::time::Duration;

/// Random values tried for the free symbols of an alternative.
const TRIALS: usize = 4;

/// The value of the expression `expr` in `set` with `env`: a float in `R` (by `approx`), the exact printed value
/// otherwise.
fn value(set: SetChoice, env: &Environment, expr: &str) -> Option<String> {
    if set == SetChoice::R {
        number(env, expr).map(|v| v.to_string())
    } else {
        let mut env = env.clone();
        common::guard::no_panic(|| eval_in(set, &mut env, expr)).and_then(Result::ok)
    }
}

/// Whether two values of [`value`] are equal.
fn same(set: SetChoice, a: &str, b: &str) -> bool {
    if set == SetChoice::R {
        close(parse_number(a).unwrap(), parse_number(b).unwrap(), 1e-9)
    } else {
        a == b
    }
}

/// Check the system `input`: `set; system` or `set; system; known solution` (like `x = 1, y = 2`).
fn solve(input: &str) -> Verdict {
    let parts: Vec<_> = input.split(';').map(str::trim).collect();
    let set: SetChoice = parts[0].parse().unwrap();
    let system = parts[1];
    let known = parts.get(2).copied();
    let output = match eval_in(set, &mut Environment::new(), system) {
        Ok(res) => res,
        Err(e) => return Verdict::Skip(e),
    };
    // `solve(eq, ..., x, y)` or plain equations
    let items = system
        .strip_prefix("solve(")
        .and_then(|s| s.strip_suffix(')'))
        .map_or_else(|| split_top(system, ','), |s| split_top(s, ','));
    let equations: Vec<(String, String)> = items
        .iter()
        .filter_map(|item| item.split_once('=').map(|(l, r)| (l.trim().to_owned(), r.trim().to_owned())))
        .collect();
    if output == "no solution" {
        return match known {
            Some(known) => Verdict::Wrong(format!("no solution, but {known} is one")),
            None => Verdict::Skip("no solution".to_owned()),
        };
    }
    if output == "true" {
        return Verdict::Skip("true".to_owned());
    }
    let mut rng = case_rng(input);
    let mut checked = 0;
    let mut alternatives = Vec::new();
    for line in output.lines().filter(|l| !l.contains('∈')) {
        let assignments: Vec<(String, String)> = split_top(line, ',')
            .iter()
            .map(|a| {
                let (u, v) = a.split_once(" = ").unwrap_or_else(|| panic!("bad assignment `{a}` in `{output}`"));
                (u.trim().to_owned(), v.trim().to_owned())
            })
            .collect();
        let assigned: Vec<_> = assignments.iter().map(|(u, _)| u.clone()).collect();
        // Free unknowns, parameters, integers
        let mut free: Vec<String> = assignments.iter().flat_map(|(_, v)| symbols(v)).collect();
        free.extend(equations.iter().flat_map(|(l, r)| symbols(&format!("{l} + {r}"))));
        free.retain(|s| !assigned.contains(s) && s != "i");
        free.sort();
        free.dedup();
        for _ in 0..TRIALS {
            let mut env = Environment::new();
            let mut point = Vec::new();
            for s in &free {
                let v = if s == "k" || s.starts_with("k_") || s.starts_with("t_") {
                    rng.range(-3, 3).to_string()
                } else if let SetChoice::Zn(n) = set {
                    rng.range(0, n as i64 - 1).to_string()
                } else if set == SetChoice::Z {
                    rng.range(-5, 5).to_string()
                } else {
                    common::numeric::Domain::Any.sample(&mut rng)
                };
                eval_in(set, &mut env, &format!("{s} := {v}")).unwrap();
                point.push(format!("{s} = {v}"));
            }
            let mut defined = true;
            for (u, v) in &assignments {
                if eval_in(set, &mut env, &format!("{u} := ({v})")).is_err() {
                    defined = false;
                }
            }
            if !defined {
                continue;
            }
            for (l, r) in &equations {
                let (Some(lv), Some(rv)) = (value(set, &env, l), value(set, &env, r)) else {
                    continue;
                };
                if !same(set, &lv, &rv) {
                    return Verdict::Wrong(format!(
                        "`{line}` doesn't satisfy `{l} = {r}`: {lv} vs {rv} at {}",
                        point.join(", ")
                    ));
                }
                checked += 1;
            }
        }
        if free.iter().all(|s| !assigned.contains(s)) && symbols(&line.replace(" = ", " + ")).len() == assigned.len() {
            alternatives.push(assignments);
        }
    }
    // A known solution is one of the alternatives (when they are points)
    if let Some(known) = known
        && output.lines().filter(|l| !l.contains('∈')).count() == alternatives.len()
    {
        let known: Vec<(String, String)> = split_top(known, ',')
            .iter()
            .map(|a| {
                let (u, v) = a.split_once('=').unwrap();
                (u.trim().to_owned(), v.trim().to_owned())
            })
            .collect();
        let env = Environment::new();
        let found = alternatives.iter().any(|alt| {
            known.iter().all(|(u, v)| {
                // An unknown without value in the alternative is free
                alt.iter().find(|(w, _)| w == u).is_none_or(|(_, value_u)| {
                    match (value(set, &env, value_u), value(set, &env, v)) {
                        (Some(a), Some(b)) => same(set, &a, &b),
                        _ => true,
                    }
                })
            })
        });
        if !found {
            return Verdict::Wrong(format!("the solution {known:?} is missing from `{output}`"));
        }
    }
    if checked > 0 {
        Verdict::Pass
    } else {
        Verdict::Skip(format!("nothing checked in `{output}`"))
    }
}

#[test]
fn systems() {
    check_all(
        "solve",
        &[
            "R; x + y = 3, x - y = 1",
            "R; x^2 - 3*x + 2 = 0",
            "R; x^2 + y^2 = 1, x = y",
            "R; x*y = 1, x + y = 3",
            "R; solve(a*x + y = 1, x - y = b, x, y)",
            "R; solve(x^2 + a*x + 1 = 0, x)",
            "R; x + y + z = 1, x - y = 2",
            "R; x^3 - 6*x^2 + 11*x - 6 = 0",
            "R; x^4 - 5*x^2 + 4 = 0",
            "R; x^3 = 2",
            "R; x^4 + x + 1 = 3",
            "R; sin(x) = 1/2",
            "R; exp(2*x) - 3*exp(x) + 2 = 0",
            "R; x*exp(x) = 1",
            "R; sqrt(x) = x - 2",
            "R; 1/x + 1/(x - 1) = 1",
            "C; x + i*y = 1, x - y = i",
            "Z/7; 3*x = 1",
            "Z/12; 4*x = 8",
            "Z/7; x^2 = 2",
            "Z; 2*x + 4*y = 6",
            "Z; x + y = 3, x + 2*y = 5",
            "R; x^2 = 4, y = x + 1; x = 2, y = 3",
        ],
        solve,
    );
}

/// A random polynomial system in `x`, `y` with a known rational solution.
fn polynomial_system(rng: &mut Rng) -> String {
    let (x0, y0) = (random::constant(rng), random::constant(rng));
    let mut equations = Vec::new();
    for _ in 0..rng.range(1, 2) {
        let degree = rng.range(1, 2) as usize;
        let p = random::polynomial(rng, &["x", "y"], degree, 3);
        let at = p.replace('x', &format!("({x0})")).replace('y', &format!("({y0})"));
        equations.push(format!("{p} = {at}"));
    }
    if equations.len() == 1 {
        // Pin `y` so the solution set is finite
        equations.push(format!("y = {y0}"));
    }
    format!("R; {}; x = {x0}, y = {y0}", equations.join(", "))
}

/// A random univariate polynomial equation with a known rational root.
fn univariate_equation(rng: &mut Rng) -> String {
    let x0 = random::constant(rng);
    let degree = rng.range(2, 4) as usize;
    let p = random::univariate(rng, "x", degree, 5);
    let at = p.replace('x', &format!("({x0})"));
    format!("R; {p} = {at}; x = {x0}")
}

/// A random linear system modulo a small `n`, with a known solution.
fn modular_system(rng: &mut Rng) -> String {
    let n = *rng.pick(&[5, 6, 7, 8, 9, 12]);
    let (x0, y0) = (rng.range(0, n - 1), rng.range(0, n - 1));
    let mut equations = Vec::new();
    for _ in 0..rng.range(1, 2) {
        let (a, b) = (rng.range(0, n - 1), rng.range(0, n - 1));
        equations.push(format!("{a}*x + {b}*y = {}", (a * x0 + b * y0) % n));
    }
    format!("Z/{n}; {}", equations.join(", "))
}

/// A random transcendental equation in `x` with a known solution `x0` (the right side is the left side at `x0`).
fn transcendental(rng: &mut Rng) -> String {
    let f = rng.pick(&["sin", "cos", "tan", "exp", "ln", "sqrt", "atan", "sinh"]);
    let (a, b) = (rng.nonzero(3), rng.range(-3, 3));
    let (p, q) = rng.rational_in(0.2, 2.0);
    let x0 = format!("{p}/{q}");
    let inner = |x: &str| format!("({a}*{x} + {b})");
    // Domains of `ln`, `sqrt`
    let shift = if matches!(*f, "ln" | "sqrt") { format!("abs({}) + 1", inner("x")) } else { inner("x") };
    let shift0 = if matches!(*f, "ln" | "sqrt") { format!("abs({}) + 1", inner(&x0)) } else { inner(&x0) };
    if rng.chance(0.5) {
        format!("R; {f}({shift}) = {f}({shift0})")
    } else {
        format!("R; {f}({shift})^2 - {f}({shift}) = {f}({shift0})^2 - {f}({shift0})")
    }
}

#[test]
#[ignore = "fuzz: random polynomial systems, run with --ignored"]
fn fuzz_polynomial_systems() {
    fuzz("fuzz polynomial systems", 60, polynomial_system, solve);
}

#[test]
#[ignore = "fuzz: random univariate equations, run with --ignored"]
fn fuzz_univariate() {
    fuzz("fuzz univariate equations", 60, univariate_equation, solve);
}

#[test]
#[ignore = "fuzz: random modular systems, run with --ignored"]
fn fuzz_modular() {
    fuzz("fuzz modular systems", 60, modular_system, solve);
}

#[test]
#[ignore = "fuzz: random transcendental equations, run with --ignored"]
fn fuzz_transcendental() {
    fuzz("fuzz transcendental equations", 60, transcendental, solve);
}

fn regression(input: &str) {
    assert_pass(input, Duration::from_secs(60), solve);
}

#[test]
#[ignore = "bug: x^2 - 3/2 = 0 in C panics on a debug assertion (as_fraction of an unnormalized term in split_complex)"]
fn bug_solve_irrational_roots_in_c_panic() {
    regression("C; x^2 - 3/2 = 0");
}

#[test]
#[ignore = "bug: exp(2*x - 2) - exp(x - 1) = 2 is rejected as not polynomial (exp(2*x) - exp(x) = 2 is solved)"]
fn bug_solve_shifted_exponential_kernel() {
    regression("R; exp(2*x - 2) - exp(x - 1) = 2; x = 1 + ln(2)");
}
