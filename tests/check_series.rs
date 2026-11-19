//! Series checked numerically: the difference between `f` and `series(f, x, a, n)` is `O((x - a)^n)`, so its
//! ratio to `h^n` stays bounded as `h -> 0` (at infinity, the ratio to `x^-n` as `x -> oo`).
mod common;

use common::{
    harness::{Verdict, check_all, fuzz},
    numeric::{Function, env_with, eval},
    random,
    rng::Rng,
};
use formalith::parser::environment::Environment;

/// Growth of the ratio between successive points (each 10 times closer) above which the remainder is too big:
/// a missing term `c h^m`, `m <= n - 1/2`, multiplies the ratio by at least `10^(1/2)`... per step, so this
/// detects missing integer powers. Fractional exponents could slip under it.
const GROWTH: f64 = 4.0;

/// Check `series(f, x, a, n)` for `input` = `f; a; n` (one sided `f; a; n; side`).
fn series(input: &str) -> Verdict {
    let parts: Vec<_> = input.split(';').map(str::trim).collect();
    let (f, a, n) = (parts[0], parts[1], parts[2]);
    let side: Option<i64> = parts.get(3).map(|s| s.parse().unwrap());
    let mut env = env_with(&[]);
    let call = side.map_or_else(|| format!("series({f}, x, {a}, {n})"), |s| format!("series({f}, x, {a}, {n}, {s})"));
    let s = match eval(&mut env, &call) {
        Ok(res) if !res.contains("series(") => res,
        Ok(res) => return Verdict::Skip(format!("unevaluated: {res}")),
        Err(e) => return Verdict::Skip(e),
    };
    remainder(&env, f, &s, a, n, side)
}

/// Check that `f - s` is `O((x - a)^n)` numerically.
fn remainder(env: &Environment, f: &str, s: &str, a: &str, n: &str, side: Option<i64>) -> Verdict {
    let mut env = env.clone();
    let (Ok(fun), Ok(ser)) = (Function::new_in(&mut env, f, &["x"]), Function::new_in(&mut env, s, &["x"])) else {
        return Verdict::Skip(format!("can't define `{s}`"));
    };
    let infinite = a == "oo" || a == "-oo";
    let sides: Vec<i64> = side.map_or_else(|| if infinite { vec![1] } else { vec![1, -1] }, |s| vec![s]);
    let mut checked = false;
    for sign in sides {
        let mut ratios = Vec::new();
        for e in [2, 3, 4] {
            let (x, scale) = if infinite {
                let x = format!("{}10^{e}", if a == "-oo" { "-" } else { "" });
                (x.clone(), format!("({x})^({n})"))
            } else {
                let h = format!("{sign}/10^{e}");
                (format!("({a}) + {h}"), format!("1/({h})^({n})"))
            };
            let diff = format!("({} - {})*{scale}", fun.call(&[x.clone()]), ser.call(&[x]));
            match ser.number_of(&diff) {
                Some(r) => ratios.push(r.abs()),
                None => break,
            }
        }
        if ratios.len() < 3 {
            continue;
        }
        checked = true;
        if ratios[2] > GROWTH * ratios[1] + 1e-9 && ratios[1] > GROWTH * ratios[0] + 1e-9 {
            return Verdict::Wrong(format!("S = {s}: |f - S|/h^n grows like {ratios:?} on side {sign}"));
        }
    }
    if checked { Verdict::Pass } else { Verdict::Skip(format!("can't evaluate f - S for S = {s}")) }
}

#[test]
fn remainder_detects_missing_terms() {
    let env = env_with(&[]);
    let wrong = |f, s, a, n| matches!(remainder(&env, f, s, a, n, None), Verdict::Wrong(_));
    assert!(wrong("sin(x)", "x - x^3/6", "0", "7"));
    assert!(!wrong("sin(x)", "x - x^3/6 + x^5/120", "0", "7"));
    assert!(wrong("exp(x)", "1 + x + x^2/2 + x^3/6", "0", "5"));
    assert!(wrong("ln(x)", "x - 1", "1", "3"));
    assert!(!wrong("ln(x)", "x - 1", "1", "2"));
    assert!(!wrong("ln(x)", "(x - 1) - (x - 1)^2/2", "1", "3"));
    assert!(wrong("1/(x^2 + 1)", "1/x^2", "oo", "5"));
    assert!(!wrong("1/(x^2 + 1)", "1/x^2 - 1/x^4", "oo", "5"));
    assert!(wrong("1/(1 - x)", "1 + x + x^2 + x^3 + 2*x^4", "0", "5"));
}

#[test]
fn expansions() {
    check_all(
        "series",
        &[
            "sin(x); 0; 6",
            "exp(x); 0; 5",
            "1/(1 - x); 0; 6",
            "ln(1 + x); 0; 5",
            "tan(x); 0; 7",
            "sqrt(1 + x); 0; 4",
            "exp(sin(x)); 0; 5",
            "1/sin(x); 0; 3",
            "cos(x)/x^2; 0; 2",
            "atan(x); 0; 6",
            "ln(x); 1; 4",
            "exp(x); 2; 4",
            "1/(x^2 + 1); oo; 6",
            "sqrt(x^2 + 1) - x; oo; 5",
            "x*ln(1 + 1/x); oo; 4",
            "sqrt(x); 0; 3; 1",
            "x^x; 0; 3; 1",
            "gamma(x); 1; 3",
            "erf(x); 0; 6",
            "sinh(x)/x; 0; 6",
            "(1 + x)^(1/3); 0; 4",
        ],
        series,
    );
}

/// A random function analytic at a random point, or with a simple pole.
fn series_case(rng: &mut Rng) -> String {
    let a = *rng.pick(&["0", "1", "-1", "1/2"]);
    let n = rng.range(2, 5);
    let f = random::expr(rng, &["x"], 3);
    if rng.chance(0.2) {
        format!("{f}/(x - {a}); {a}; {n}")
    } else {
        format!("{f}; {a}; {n}")
    }
}

#[test]
#[ignore = "fuzz: random series, run with --ignored"]
fn fuzz_series() {
    fuzz("fuzz series", 80, series_case, series);
}
