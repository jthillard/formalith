//! Extrema checked against their definition: the value of `f` printed with each point is `f` at that point, the
//! point lies in the domain, no sampled point beats a global extremum, and no point of a small neighborhood beats a
//! local one (the difference being computed exactly by `approx`, so that degenerate extrema like `x^4` count).
mod common;

use common::{
    harness::{Verdict, assert_pass, case_rng, check_all, fuzz},
    numeric::{Domain, Function, close, env_with, eval, number, split_top, symbols},
    random,
    rng::Rng,
};
use formalith::parser::environment::Environment;
use std::time::Duration;

/// Points sampled to look for a value beating a global extremum.
const SAMPLES: usize = 40;
/// Steps of the neighborhoods of local extrema.
const STEPS: [&str; 2] = ["1/10^3", "1/10^5"];
/// Random directions of the neighborhoods of local extrema of several variables.
const DIRECTIONS: usize = 6;
/// Values of the integer `k` of periodic points.
const INTEGERS: [i64; 3] = [-1, 0, 2];

/// The arguments of `name(...)` in `input`.
fn call_args(input: &str, name: &str) -> Option<Vec<String>> {
    input
        .strip_prefix(name)?
        .strip_prefix('(')?
        .strip_suffix(')')
        .map(|args| split_top(args, ','))
}

/// One extremum of the output: its kind, the values of the variables (some may be missing, being free) and the
/// value of `f`.
struct Extremum {
    min: bool,
    point: Vec<(String, String)>,
    value: String,
}

/// The extrema printed in `output`, without the line of integers.
fn extrema(output: &str) -> Result<Vec<Extremum>, String> {
    let mut res = Vec::new();
    for line in output.lines().filter(|l| !l.contains('∈')) {
        let (min, rest) = if let Some(rest) = line.strip_prefix("min: ") {
            (true, rest)
        } else if let Some(rest) = line.strip_prefix("max: ") {
            (false, rest)
        } else {
            return Err(format!("unexpected line `{line}`"));
        };
        let mut point = Vec::new();
        for assignment in split_top(rest, ',') {
            let (u, v) = assignment
                .split_once(" = ")
                .ok_or_else(|| format!("bad assignment `{assignment}`"))?;
            point.push((u.trim().to_owned(), v.trim().to_owned()));
        }
        let (f, value) = point.pop().ok_or_else(|| format!("empty line `{line}`"))?;
        if f != "f" {
            return Err(format!("no value of `f` in `{line}`"));
        }
        res.push(Extremum { min, point, value });
    }
    Ok(res)
}

/// The problem of an input: `extrema(f, x, y)`, `extrema(f, x, a, b)` or the same with `localextrema`, possibly
/// followed by `; exists` when both extrema surely exist (continuous `f` on a closed bounded interval).
struct Problem {
    local: bool,
    f: String,
    vars: Vec<String>,
    /// Bounds of the single variable, as numbers (infinite when absent).
    bounds: (f64, f64),
    /// The bounds as expressions, when finite.
    bound_exprs: (Option<String>, Option<String>),
    exists: bool,
}

impl Problem {
    fn parse(input: &str) -> Result<Self, String> {
        let (statement, exists) = match input.split_once(';') {
            Some((s, flag)) => (s.trim(), flag.trim() == "exists"),
            None => (input.trim(), false),
        };
        let (local, args) = if let Some(args) = call_args(statement, "localextrema") {
            (true, args)
        } else if let Some(args) = call_args(statement, "extrema") {
            (false, args)
        } else {
            return Err(format!("not an extrema statement: `{statement}`"));
        };
        let f = args[0].clone();
        let env = Environment::new();
        let bound = |e: &str, default: f64| match e {
            "oo" => Ok((f64::INFINITY, None)),
            "-oo" => Ok((f64::NEG_INFINITY, None)),
            _ => number(&env, e)
                .map(|v| (v, Some(e.to_owned())))
                .ok_or_else(|| format!("bound `{e}` isn't a number ({default})")),
        };
        let (vars, bounds, bound_exprs) = if args.len() == 4 {
            let (a, ea) = bound(&args[2], f64::NEG_INFINITY)?;
            let (b, eb) = bound(&args[3], f64::INFINITY)?;
            (vec![args[1].clone()], (a, b), (ea, eb))
        } else {
            let mut vars: Vec<_> = args[1..].to_vec();
            if vars.is_empty() {
                vars = symbols(&f);
                vars.sort();
            }
            (vars, (f64::NEG_INFINITY, f64::INFINITY), (None, None))
        };
        Ok(Self {
            local,
            f,
            vars,
            bounds,
            bound_exprs,
            exists,
        })
    }

    /// A random point of the domain, sampled widely when it is unbounded.
    fn sample(&self, rng: &mut Rng) -> Vec<String> {
        let (a, b) = self.bounds;
        self.vars
            .iter()
            .map(|_| {
                let (lo, hi) = match (a.is_finite(), b.is_finite()) {
                    (true, true) => (a, b),
                    (true, false) => (a, a + if rng.chance(0.2) { 100.0 } else { 10.0 }),
                    (false, true) => (b - if rng.chance(0.2) { 100.0 } else { 10.0 }, b),
                    (false, false) if rng.chance(0.2) => (-100.0, 100.0),
                    (false, false) => (-6.0, 6.0),
                };
                let (p, q) = rng.rational_in(0.0, 1.0);
                // `lo + (hi - lo) p/q`, exactly
                format!("({lo}) + ({})*{p}/{q}", hi - lo)
            })
            .collect()
    }
}

/// Check the output of the extrema statement `input`.
fn optimize(input: &str) -> Verdict {
    let statement = input.split(';').next().unwrap().trim();
    match eval(&mut Environment::new(), statement) {
        Ok(output) => verify(input, &output),
        Err(e) => Verdict::Skip(e),
    }
}

/// Check that `output` is a correct result of the extrema statement `input`.
fn verify(input: &str, output: &str) -> Verdict {
    let problem = match Problem::parse(input) {
        Ok(p) => p,
        Err(e) => return Verdict::Wrong(e),
    };
    let found = if output.trim() == "no extremum" {
        Vec::new()
    } else {
        match extrema(output) {
            Ok(found) => found,
            Err(e) => return Verdict::Wrong(format!("{e} in `{output}`")),
        }
    };
    if problem.exists && !problem.local {
        for min in [true, false] {
            if !found.iter().any(|e| e.min == min) {
                let kind = if min { "minimum" } else { "maximum" };
                return Verdict::Wrong(format!("no {kind} in `{output}`, but it exists"));
            }
        }
    }
    if found.is_empty() {
        return Verdict::Skip(format!("no extremum: `{output}`"));
    }
    let mut rng = case_rng(input);
    let mut checked = 0;
    for extremum in &found {
        let integers: &[i64] = if output.contains('∈') {
            &INTEGERS
        } else {
            &[0]
        };
        for &k in integers {
            match check_extremum(&problem, extremum, k, &mut rng) {
                Ok(n) => checked += n,
                Err(e) => return Verdict::Wrong(e),
            }
        }
    }
    if checked > 0 {
        Verdict::Pass
    } else {
        Verdict::Skip(format!("nothing checked in `{output}`"))
    }
}

/// Check one extremum with the integer `k` (of periodic points), giving the number of checked facts.
fn check_extremum(
    problem: &Problem,
    extremum: &Extremum,
    k: i64,
    rng: &mut Rng,
) -> Result<usize, String> {
    let kind = if extremum.min { "min" } else { "max" };
    // The free variables get random values, then the point is evaluated
    let mut env = env_with(&[&format!("k := {k}")]);
    let mut point = Vec::new();
    for var in &problem.vars {
        let value = match extremum.point.iter().find(|(u, _)| u == var) {
            Some((_, v)) => v.clone(),
            None => {
                let v = Domain::Range(-3.0, 3.0).sample(rng);
                eval(&mut env, &format!("{var} := {v}"))?;
                v
            }
        };
        point.push(value);
    }
    // Values in terms of free variables are expanded through the definitions
    let point: Vec<String> = point
        .iter()
        .map(|v| {
            let mut env = env.clone();
            eval(&mut env, v).unwrap_or_else(|_| v.clone())
        })
        .collect();
    let vars: Vec<&str> = problem.vars.iter().map(String::as_str).collect();
    let f = Function::new_in(&mut env, &problem.f, &vars)?;
    let at = |args: &[String]| number(&env, &f.call(args));
    let Some(value) = number(&env, &extremum.value) else {
        return Ok(0);
    };
    let mut checked = 0;
    let Some(actual) = at(&point) else {
        return Err(format!(
            "{kind} at {point:?} (k = {k}), where f = {} isn't defined",
            problem.f
        ));
    };
    if !close(actual, value, 1e-9) {
        return Err(format!(
            "{kind} at {point:?} (k = {k}) printed with f = {value}, but f = {actual} there"
        ));
    }
    checked += 1;
    let (a, b) = problem.bounds;
    if problem.vars.len() == 1 {
        let x = number(&env, &point[0]).ok_or_else(|| format!("point {point:?} isn't a number"))?;
        if x < a - 1e-12 || x > b + 1e-12 {
            return Err(format!("{kind} at x = {x}, outside of [{a}, {b}]"));
        }
    }
    // Whether `other` beats the extremum, `difference` being `f(other) - f(point)`
    let beats = |difference: f64| {
        if extremum.min {
            difference < 0.0
        } else {
            difference > 0.0
        }
    };
    if problem.local {
        // Neighbors, inside the bounds
        let directions: Vec<Vec<i64>> = if problem.vars.len() == 1 {
            vec![vec![1], vec![-1]]
        } else {
            (0..DIRECTIONS)
                .map(|_| problem.vars.iter().map(|_| rng.range(-3, 3)).collect())
                .filter(|d: &Vec<i64>| d.iter().any(|&c| c != 0))
                .collect()
        };
        for h in STEPS {
            for direction in &directions {
                let neighbor: Vec<String> = point
                    .iter()
                    .zip(direction)
                    .map(|(p, d)| format!("({p}) + ({d})*{h}"))
                    .collect();
                if problem.vars.len() == 1 {
                    let x = number(&env, &neighbor[0]).unwrap_or(f64::NAN);
                    if !(a..=b).contains(&x) {
                        continue;
                    }
                }
                let difference = format!("{} - {}", f.call(&neighbor), f.call(&point));
                // Exactly, then approximated: its sign is right
                let Some(d) = number(&env, &difference) else {
                    continue;
                };
                if beats(d) && d.abs() > 1e-25 {
                    return Err(format!(
                        "local {kind} at {point:?} (k = {k}), but f({neighbor:?}) - f = {d}"
                    ));
                }
                checked += 1;
            }
        }
    } else {
        // Bounds, then random points
        let mut candidates: Vec<Vec<String>> = Vec::new();
        for e in [&problem.bound_exprs.0, &problem.bound_exprs.1]
            .into_iter()
            .flatten()
        {
            candidates.push(vec![e.clone()]);
        }
        candidates.extend((0..SAMPLES).map(|_| problem.sample(rng)));
        for other in candidates {
            let Some(v) = at(&other) else {
                continue;
            };
            if beats(v - value) && !close(v, value, 1e-9) {
                return Err(format!(
                    "global {kind} f = {value} at {point:?}, but f({other:?}) = {v}"
                ));
            }
            checked += 1;
        }
    }
    Ok(checked)
}

#[test]
fn oracle_detects_wrong_extrema() {
    // A wrong value of `f`
    assert!(matches!(
        verify("extrema(x^2, x)", "min: x = 0, f = 1"),
        Verdict::Wrong(_)
    ));
    // A point beaten by another one
    assert!(matches!(
        verify("extrema(x^2 - 2*x, x)", "min: x = 0, f = 0"),
        Verdict::Wrong(_)
    ));
    // Outside of the bounds
    assert!(matches!(
        verify(
            "extrema(x, x, 0, 1)",
            "min: x = -1, f = -1\nmax: x = 1, f = 1"
        ),
        Verdict::Wrong(_)
    ));
    // Not a local minimum (an inflection point)
    assert!(matches!(
        verify("localextrema(x^3, x)", "min: x = 0, f = 0"),
        Verdict::Wrong(_)
    ));
    // A missing extremum of a continuous function on a closed interval
    assert!(matches!(
        verify("extrema(x^2, x, -1, 2); exists", "min: x = 0, f = 0"),
        Verdict::Wrong(_)
    ));
    // Correct ones
    assert!(matches!(
        verify("localextrema(x^4, x)", "min: x = 0, f = 0"),
        Verdict::Pass
    ));
    assert!(matches!(
        verify(
            "extrema(cos(x), x)",
            "min: x = pi + 2*pi*k, f = -1\nmax: x = 2*pi*k, f = 1\nk ∈ ℤ"
        ),
        Verdict::Pass
    ));
}

#[test]
fn global_extrema() {
    check_all(
        "extrema",
        &[
            "extrema(x^2 - 2*x, x, 0, 3); exists",
            "extrema(x^3 - 3*x, x, -3, 3); exists",
            "extrema(x^3 - 3*x, x, -2, 3); exists",
            "extrema(sin(x), x, 0, 4); exists",
            "extrema(x/(x^2 + 1), x)",
            "extrema(x*exp(-x), x)",
            "extrema(x*ln(x), x)",
            "extrema(cos(x), x)",
            "extrema(x^4 - 2*x^2, x)",
            "extrema(sqrt(x), x)",
            "extrema(x^2 + 1/x^2, x)",
            "extrema(abs(x^2 - 1) + x, x)",
            "extrema(abs(x) - x^2, x)",
            "extrema(1/x, x, 1, 2); exists",
            "extrema(x^2, x, 1, oo)",
            "extrema(x^2 + y^2 - 2*x, x, y)",
            "extrema(-x^2 - (y - 1)^2, x, y)",
            "extrema((x - y)^2, x, y)",
            "extrema(x^(1/3)*(x - 4), x)",
            "extrema(acosh(x) - x/2, x)",
            "extrema(tan(x) - 2*x, x, -1, 1); exists",
        ],
        optimize,
    );
}

#[test]
fn local_extrema() {
    check_all(
        "localextrema",
        &[
            "localextrema(x^3 - 3*x, x)",
            "localextrema(x^4 - 2*x^2, x)",
            "localextrema(x^4, x)",
            "localextrema(x^3 - 3*x, x, -3, 3)",
            "localextrema(x, x, 0, 1)",
            "localextrema(abs(x), x)",
            "localextrema(sqrt(x), x)",
            "localextrema(x^2 + 1/x^2, x)",
            "localextrema(x*exp(-x), x)",
            "localextrema(cos(x), x)",
            "localextrema(x + 2*sin(x), x)",
            "localextrema(x^3 - 3*x + y^2, x, y)",
            "localextrema(-x^2 - y^2 + 2*y, x, y)",
            "localextrema(exp(x^2 + y^2), x, y)",
            "localextrema((x - y)^2, x, y)",
            "localextrema(atanh(x) - 2*x, x)",
            "localextrema(tan(x) - 2*x, x, -1, 1)",
            "localextrema(x^(1/3)*(x - 4), x)",
        ],
        optimize,
    );
}

/// Random bounds `a < b` (small integers or fractions), or none.
fn bounds(rng: &mut Rng) -> Option<(String, String)> {
    if rng.chance(0.4) {
        return None;
    }
    let a = rng.range(-4, 2);
    let b = a + rng.range(1, 5);
    let (a, b) = if rng.chance(0.3) {
        (format!("{}/2", 2 * a - 1), b.to_string())
    } else {
        (a.to_string(), b.to_string())
    };
    Some(match rng.below(5) {
        0 => (a, "oo".to_owned()),
        1 => ("-oo".to_owned(), b),
        _ => (a, b),
    })
}

/// A statement `name(f, x)` or `name(f, x, a, b)`, flagged `exists` for continuous `f` on closed bounds.
fn univariate_statement(rng: &mut Rng, name: &str, f: &str, continuous: bool) -> String {
    match bounds(rng) {
        Some((a, b)) => {
            let closed = !a.contains("oo") && !b.contains("oo");
            let flag = if continuous && closed { "; exists" } else { "" };
            format!("{name}({f}, x, {a}, {b}){flag}")
        }
        None => format!("{name}({f}, x)"),
    }
}

/// A random function of one variable: polynomials (continuous), rational functions, products with `exp`, `ln`,
/// `abs`, trigonometric functions.
fn univariate_case(rng: &mut Rng, name: &str) -> String {
    let degree = rng.range(2, 5) as usize;
    let p = random::univariate(rng, "x", degree, 5);
    match rng.below(7) {
        0 | 1 => univariate_statement(rng, name, &p, true),
        2 => {
            let degree = rng.range(1, 2) as usize;
            let q = random::univariate(rng, "x", degree, 4);
            univariate_statement(rng, name, &format!("{p}/{q}"), false)
        }
        3 => {
            let e = format!("{p}*exp({}*x)", rng.nonzero(2));
            univariate_statement(rng, name, &e, true)
        }
        4 => {
            let e = format!("{}*ln(x) + {}", random::linear(rng, "x"), rng.nonzero(3));
            format!("{name}({e}, x)")
        }
        5 => {
            let e = format!(
                "abs({}) + {}",
                random::linear(rng, "x"),
                random::univariate(rng, "x", 2, 3)
            );
            univariate_statement(rng, name, &e, true)
        }
        _ => {
            let trig = rng.pick(&["sin", "cos"]);
            let e = format!("{}*x + {}*{trig}(x)", rng.range(-1, 1), rng.nonzero(3));
            univariate_statement(rng, name, &e, true)
        }
    }
}

/// A random polynomial in `x`, `y` of degree 2 to 4, made bounded below often.
fn bivariate_case(rng: &mut Rng, name: &str) -> String {
    let p = random::polynomial(rng, &["x", "y"], 3, 3);
    let f = if rng.chance(0.5) {
        format!("x^4 + y^4 + {p}")
    } else {
        format!("{}*x^2 + {}*y^2 + {p}", rng.range(1, 3), rng.range(1, 3))
    };
    format!("{name}({f}, x, y)")
}

#[test]
#[ignore = "fuzz: random functions of one variable, run with --ignored"]
fn fuzz_extrema() {
    fuzz(
        "fuzz extrema",
        60,
        |rng| univariate_case(rng, "extrema"),
        optimize,
    );
}

#[test]
#[ignore = "fuzz: random functions of one variable, run with --ignored"]
fn fuzz_local_extrema() {
    fuzz(
        "fuzz localextrema",
        60,
        |rng| univariate_case(rng, "localextrema"),
        optimize,
    );
}

#[test]
#[ignore = "fuzz: random polynomials of two variables, run with --ignored"]
fn fuzz_bivariate() {
    fuzz(
        "fuzz bivariate extrema",
        40,
        |rng| {
            let name = if rng.chance(0.5) {
                "extrema"
            } else {
                "localextrema"
            };
            bivariate_case(rng, name)
        },
        optimize,
    );
}

fn regression(input: &str) {
    assert_pass(input, Duration::from_secs(60), optimize);
}

#[test]
fn bug_critical_points_of_polynomial_times_exponential() {
    // `f'` is `{$e^(2x) (10 x^2 + 10 x - 2)$}` expanded, whose exponential wasn't factored out
    regression("extrema((5*x^2 - 1)*exp(2*x), x, 1, 2); exists");
    regression("extrema((x^2 + 2*x - 5)*exp(x), x)");
}
