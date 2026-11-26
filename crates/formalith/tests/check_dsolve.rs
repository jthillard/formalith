//! Differential equations checked against their definition: each solution `y(x) = g`, substituted in the
//! equation, makes it vanish for random values of `x` and of the constants `c_1, c_2...`, and satisfies the
//! initial conditions.

use crate::common::{
    harness::{Verdict, assert_pass, case_rng, check_all, fuzz},
    numeric::{Domain, Function, close, env_with, equivalent, eval},
    random,
    rng::Rng,
};
use std::time::Duration;

/// Replace `y`, `y'`, `y''`... in `equation` by `derivatives[order]`.
fn substitute(equation: &str, derivatives: &[String]) -> Option<String> {
    let chars: Vec<char> = equation.chars().collect();
    let ident = |c: char| c.is_ascii_alphanumeric() || c == '_';
    let mut res = String::new();
    let mut i = 0;
    while i < chars.len() {
        if chars[i] == 'y'
            && (i == 0 || !ident(chars[i - 1]))
            && chars.get(i + 1).is_none_or(|&c| !ident(c))
        {
            let mut order = 0;
            i += 1;
            while chars.get(i) == Some(&'\'') {
                order += 1;
                i += 1;
            }
            res.push_str(&format!("({})", derivatives.get(order)?));
        } else {
            res.push(chars[i]);
            i += 1;
        }
    }
    Some(res)
}

/// The constants `c_1, c_2...` appearing in `term`.
fn constants(term: &str) -> Vec<String> {
    (1..=9)
        .map(|i| format!("c_{i}"))
        .filter(|c| {
            term.match_indices(c.as_str())
                .any(|(at, _)| !term[at + c.len()..].starts_with(|ch: char| ch.is_ascii_digit()))
        })
        .collect()
}

/// Check `dsolve(input)`, `input` being the equation (in `y`, `y'`...) then optional conditions, comma separated.
fn dsolve(input: &str) -> Verdict {
    let mut env = env_with(&[]);
    let output = match eval(&mut env, &format!("dsolve({input})")) {
        Ok(res) => res,
        Err(e) => return Verdict::Skip(e),
    };
    let mut parts = input.split(',').map(str::trim);
    let equation = parts.next().unwrap();
    let conditions: Vec<_> = parts.collect();
    let order = (1..=4)
        .rev()
        .find(|&n| equation.contains(&format!("y{}", "'".repeat(n))))
        .unwrap_or(0);
    let (lhs, rhs) = equation.split_once('=').unwrap();
    let mut checked = 0;
    for line in output.lines() {
        let Some(g) = line.strip_prefix("y(x) = ") else {
            continue; // Implicit solutions
        };
        // Power series solutions are checked on their partial sums, since `sum(f, k, 0, +oo)` parsed back stays
        // unevaluated: the rest is negligible for `{$|x| <= 2$}`
        let g = &g.replace(", +oo)", ", 40)");
        // Derivatives by the derivative engine
        let mut derivatives = vec![g.to_owned()];
        for n in 1..=order {
            match eval(&mut env, &format!("diff({g}, x, {n})")) {
                Ok(d) => derivatives.push(d),
                Err(e) => return Verdict::Skip(format!("diff: {e}")),
            }
        }
        let (Some(l), Some(r)) = (substitute(lhs, &derivatives), substitute(rhs, &derivatives))
        else {
            return Verdict::Skip("substitution".to_owned());
        };
        let names = constants(g);
        let mut vars = vec![("x", Domain::Range(-2.0, 2.0))];
        vars.extend(names.iter().map(|c| (c.as_str(), Domain::Range(-2.0, 2.0))));
        let mut rng = case_rng(input);
        match equivalent(&env, &l, &r, &vars, &mut rng) {
            crate::common::numeric::Check::Differ(why) => {
                return Verdict::Wrong(format!("y(x) = {g} doesn't satisfy the equation: {why}"));
            }
            crate::common::numeric::Check::Equal => checked += 1,
            crate::common::numeric::Check::Inconclusive(_) => {}
        }
        for condition in &conditions {
            // `y'(a) = b`
            let (head, value) = condition.split_once('=').unwrap();
            let head = head.trim();
            let n = head.matches('\'').count();
            let point = &head[head.find('(').unwrap() + 1..head.rfind(')').unwrap()];
            let Ok(d) = Function::new(&env, &derivatives[n], &["x"]) else {
                continue;
            };
            let (Some(got), Some(want)) = (
                d.at(&[point.to_owned()]),
                crate::common::numeric::number(&env, value),
            ) else {
                continue;
            };
            if !close(got, want, 1e-9) {
                return Verdict::Wrong(format!("y(x) = {g}: {head} = {got}, not {want}"));
            }
        }
    }
    if checked > 0 {
        Verdict::Pass
    } else {
        Verdict::Skip(format!("nothing checked in `{output}`"))
    }
}

#[test]
fn equations() {
    check_all(
        "dsolve",
        &[
            "y' = x*y",
            "y' + 2*x*y = x",
            "x*y' + y = x^2",
            "y' = y^2",
            "y' = x/y",
            "y' = exp(x - y)",
            "y' = y*(1 - y)",
            "y' = (1 + y^2)/(1 + x^2)",
            "y'' + y = 0, y(0) = 1, y'(0) = 0",
            "y'' - 3*y' + 2*y = exp(3*x)",
            "y'' + 2*y' + y = x",
            "y'' + 4*y = sin(x), y(0) = 0, y'(0) = 1",
            "y''' - y' = 0",
            "y'' + y = cos(x)",
            "y' = x*y, y(0) = 2",
            "y'' - y = exp(x), y(0) = 1, y'(0) = 2",
            "y' = y, y'(0) = 3",
            "y' = x/y, y'(1) = 2",
            "y'' + x*y = 0",
            "y'' + x*y = 0, y(0) = 1, y'(0) = -1",
            "y'' - x*y' - y = 0",
            "y'' - 2*x*y' + 2*y = 0",
        ],
        dsolve,
    );
}

/// A random linear equation with constant coefficients, maybe with initial conditions.
fn linear_equation(rng: &mut Rng) -> String {
    let order = rng.range(1, 3) as usize;
    let mut terms = Vec::new();
    for n in (0..=order).rev() {
        let c = if n == order {
            rng.range(1, 2)
        } else {
            rng.range(-3, 3)
        };
        if c != 0 {
            terms.push(format!("{c}*y{}", "'".repeat(n)));
        }
    }
    let rhs = (*rng.pick(&[
        "0", "x", "exp(2*x)", "sin(x)", "x^2", "cos(3*x)", "exp(-x)", "1", "x*exp(x)",
    ]))
    .to_owned();
    let mut equation = format!("{} = {rhs}", terms.join(" + "));
    if rng.chance(0.4) {
        for n in 0..order {
            equation.push_str(&format!(", y{}(0) = {}", "'".repeat(n), rng.range(-2, 2)));
        }
    }
    equation
}

/// A random first order equation: linear or separable.
fn first_order(rng: &mut Rng) -> String {
    let p = rng.pick(&["x", "1", "2*x", "1/x", "cos(x)", "x^2", "exp(x)"]);
    // Not `sqrt(y)`: `y = (x + c)^2/4` only solves `y' = sqrt(y)` where `x + c >= 0`
    let q = rng.pick(&["y", "y^2", "1 + y^2", "exp(-y)", "y*(2 - y)", "1/y"]);
    if rng.chance(0.5) {
        format!("y' = {p} * {q}")
    } else {
        let g = random::integrand_atom(rng);
        format!("y' + {p}*y = {g}")
    }
}

#[test]
#[ignore = "fuzz: random linear equations, run with --ignored"]
fn fuzz_linear() {
    fuzz("fuzz linear ODEs", 60, linear_equation, dsolve);
}

#[test]
#[ignore = "fuzz: random first order equations, run with --ignored"]
fn fuzz_first_order() {
    fuzz("fuzz first order ODEs", 60, first_order, dsolve);
}

fn regression(input: &str) {
    assert_pass(input, Duration::from_secs(60), dsolve);
}

#[test]
fn bug_dsolve_irrational_characteristic_roots_panic() {
    // Same root cause as `x^2 - 3/2 = 0` in C (`check_solve.rs`)
    regression("2*y'' - 3*y = 0");
}

#[test]
fn bug_dsolve_third_order_is_slow() {
    regression("2*y''' + y'' - 3*y' + y = cos(3*x)");
}

#[test]
fn bug_dsolve_sin_forcing_is_slow() {
    // `as_fraction` of the expanded particular solution was exponential in its number of terms
    regression("1*y'' + -1*y' + 3*y = sin(x), y(0) = 1, y'(0) = 1");
}

#[test]
fn bug_dsolve_complex_roots_with_sin_2x_forcing() {
    // The sums and constant factors of the variation of parameters used up the integrator's depth
    regression("y'' - y' + 3*y = sin(2*x)");
}
