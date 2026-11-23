//! The set `C` checked against independent computations: Gaussian rational arithmetic against exact complex
//! arithmetic done in the test, and functions `f = g + i h` built with their real and imaginary parts (so `g` and
//! `h` are known) against `g` and `h` in `R`: values at points, derivatives and definite integrals.
//!
//! Principal logarithms and powers of constants are checked against `f64` polar forms.
//!
//! So as not to rely on `approx`, `re` and `im` of `C`, a result `F` is read as `A + i B` by replacing `i` by a
//! symbol `chk_i` in `R` (`A` is `F` at `chk_i = 0`, `B` the difference at `chk_i = 1`), after checking that it is
//! affine in `chk_i`.
mod common;

use common::{
    harness::{Verdict, assert_pass, case_rng, check_all, fuzz},
    numeric::{close, eval, eval_in, number},
    rng::Rng,
};
use formalith::{dynamic::SetChoice, parser::environment::Environment};
use malachite::Rational;
use std::time::Duration;

/// A Gaussian rational `a + b i`.
#[derive(Clone, Debug, PartialEq)]
struct Gaussian(Rational, Rational);

impl Gaussian {
    fn add(&self, o: &Self) -> Self {
        Self(&self.0 + &o.0, &self.1 + &o.1)
    }
    fn sub(&self, o: &Self) -> Self {
        Self(&self.0 - &o.0, &self.1 - &o.1)
    }
    fn mul(&self, o: &Self) -> Self {
        Self(
            &self.0 * &o.0 - &self.1 * &o.1,
            &self.0 * &o.1 + &self.1 * &o.0,
        )
    }
    fn div(&self, o: &Self) -> Option<Self> {
        let n = &o.0 * &o.0 + &o.1 * &o.1;
        if n == 0 {
            return None;
        }
        let conj = Self(o.0.clone(), -&o.1);
        let p = self.mul(&conj);
        Some(Self(p.0 / &n, p.1 / n))
    }
    fn text(&self) -> String {
        format!("(({}) + ({})*i)", self.0, self.1)
    }
}

/// A random Gaussian rational expression and its value, computed here.
fn gaussian_expr(rng: &mut Rng, depth: usize) -> (String, Gaussian) {
    if depth == 0 || rng.chance(0.25) {
        let r = |rng: &mut Rng| Rational::from(rng.range(-5, 5)) / Rational::from(rng.range(1, 4));
        let g = Gaussian(r(rng), r(rng));
        return (g.text(), g);
    }
    let (a, va) = gaussian_expr(rng, depth - 1);
    let (b, vb) = gaussian_expr(rng, depth - 1);
    match rng.below(6) {
        0 | 1 => (format!("({a} + {b})"), va.add(&vb)),
        2 => (format!("({a} - {b})"), va.sub(&vb)),
        3 | 4 => (format!("({a} * {b})"), va.mul(&vb)),
        _ => match va.div(&vb) {
            Some(v) => (format!("({a} / {b})"), v),
            None => (a, va),
        },
    }
}

/// Check that the Gaussian expression `input` (`expr; a; b` with its expected value `a + b i`) evaluates to it in
/// `C`, and that `conj`, `abs` squared and `re` / `im` agree.
fn gaussian(input: &str) -> Verdict {
    let parts: Vec<_> = input.split(';').map(str::trim).collect();
    let (expr, a, b) = (parts[0], parts[1], parts[2]);
    let c = |s: &str| eval_in(SetChoice::C, &mut Environment::new(), s);
    let checks = [
        (format!("({expr}) - (({a}) + ({b})*i)"), "0".to_owned()),
        (format!("conj({expr}) - (({a}) - ({b})*i)"), "0".to_owned()),
        (format!("re({expr})"), c(a).unwrap_or_default()),
        (format!("im({expr})"), c(b).unwrap_or_default()),
        (
            format!("abs({expr})^2"),
            c(&format!("({a})^2 + ({b})^2")).unwrap_or_default(),
        ),
    ];
    for (lhs, expected) in checks {
        match c(&lhs) {
            Ok(v) if v == expected => {}
            Ok(v) => return Verdict::Wrong(format!("`{lhs}` = {v}, expected {expected}")),
            Err(e) => return Verdict::Wrong(format!("`{lhs}`: {e}")),
        }
    }
    Verdict::Pass
}

/// A complex function of `x` with its real and imaginary parts.
#[derive(Clone, Debug)]
struct Parts {
    complex: String,
    re: String,
    im: String,
}

/// A random complex function of `x`, built with its parts.
fn parts(rng: &mut Rng, depth: usize) -> Parts {
    let small = |rng: &mut Rng| rng.range(-3, 3);
    if depth == 0 || rng.chance(0.3) {
        return match rng.below(4) {
            0 => Parts {
                complex: "x".into(),
                re: "x".into(),
                im: "0".into(),
            },
            1 => {
                let (a, b) = (small(rng), rng.nonzero(3));
                Parts {
                    complex: format!("({a} + {b}*i)"),
                    re: a.to_string(),
                    im: b.to_string(),
                }
            }
            2 => {
                // `{$e^((a + b i) x) = e^(a x) (cos(b x) + i sin(b x))$}`
                let (a, b) = (small(rng), rng.nonzero(3));
                Parts {
                    complex: format!("exp(({a} + {b}*i)*x)"),
                    re: format!("exp({a}*x)*cos({b}*x)"),
                    im: format!("exp({a}*x)*sin({b}*x)"),
                }
            }
            _ => {
                let f = rng.pick(&["sin", "cos", "atan", "exp"]);
                let c = rng.nonzero(2);
                Parts {
                    complex: format!("{f}({c}*x)"),
                    re: format!("{f}({c}*x)"),
                    im: "0".into(),
                }
            }
        };
    }
    let p = parts(rng, depth - 1);
    let q = parts(rng, depth - 1);
    match rng.below(4) {
        0 | 1 => Parts {
            complex: format!("({} + {})", p.complex, q.complex),
            re: format!("({} + {})", p.re, q.re),
            im: format!("({} + {})", p.im, q.im),
        },
        2 => Parts {
            complex: format!("({} * {})", p.complex, q.complex),
            re: format!("({}*{} - {}*{})", p.re, q.re, p.im, q.im),
            im: format!("({}*{} + {}*{})", p.re, q.im, p.im, q.re),
        },
        _ => Parts {
            complex: format!("conj({})", p.complex),
            re: p.re,
            im: format!("(-{})", p.im),
        },
    }
}

/// `F`, printed by `C`, as the expressions `(A, B)` with `F = A + i B` in `R`, if it is affine in `i`. `env` holds
/// the values of other symbols.
fn split(env: &Environment, output: &str) -> Option<(f64, f64)> {
    // `i` alone, not inside other identifiers
    let mut text = String::new();
    let chars: Vec<char> = output.chars().collect();
    for (j, &c) in chars.iter().enumerate() {
        let alone = |k: Option<&char>| !k.is_some_and(|c| c.is_alphanumeric() || *c == '_');
        if c == 'i' && alone(j.checked_sub(1).and_then(|k| chars.get(k))) && alone(chars.get(j + 1))
        {
            text.push_str("chk_i");
        } else {
            text.push(c);
        }
    }
    let at = |v: i64| {
        let mut env = env.clone();
        eval(&mut env, &format!("chk_i := {v}")).ok()?;
        number(&env, &text)
    };
    let (f0, f1, f2) = (at(0)?, at(1)?, at(2)?);
    // Affine: `{$F(2) - F(0) = 2 (F(1) - F(0))$}`
    if !close(f2 - f0, 2. * (f1 - f0), 1e-9) {
        return None;
    }
    Some((f0, f1 - f0))
}

/// Check the complex function of `input` (`complex; re; im`) at points, its derivative and its integral.
fn calculus(input: &str) -> Verdict {
    let parts: Vec<_> = input.split(';').map(str::trim).collect();
    let (f, re, im) = (parts[0], parts[1], parts[2]);
    let mut rng = case_rng(input);
    let mut checked = 0;
    let c = |env: &mut Environment, s: &str| {
        common::guard::no_panic(|| eval_in(SetChoice::C, env, s)).and_then(Result::ok)
    };
    // Values and derivatives at points
    for _ in 0..3 {
        let x0 = format!("{}/{}", rng.range(-7, 7), rng.range(2, 5));
        for (what, complex, re, im) in [
            ("f", f.to_owned(), re.to_owned(), im.to_owned()),
            (
                "f'",
                format!("diff({f}, x)"),
                format!("diff({re}, x)"),
                format!("diff({im}, x)"),
            ),
        ] {
            let mut env = Environment::new();
            if c(&mut env, &format!("x := {x0}")).is_none() {
                continue;
            }
            let Some(output) = c(&mut env, &complex) else {
                continue;
            };
            let real = env_with_x(&x0);
            let (Some((a, b)), Some(g), Some(h)) = (
                split(&real, &output),
                number(&real, &re),
                number(&real, &im),
            ) else {
                continue;
            };
            if !close(a, g, 1e-9) || !close(b, h, 1e-9) {
                return Verdict::Wrong(format!(
                    "{what} at x = {x0} is `{output}` = {a} + {b} i, but its parts are {g} and {h}"
                ));
            }
            checked += 1;
        }
    }
    // A definite integral
    let (lo, hi) = (rng.range(-2, 0), rng.range(1, 2));
    let integral = |g: &str| format!("integrate({g}, x, {lo}, {hi})");
    if let Some(output) = c(&mut Environment::new(), &integral(f))
        && !output.contains("integrate")
    {
        let real = Environment::new();
        if let (Some((a, b)), Some(g), Some(h)) = (
            split(&real, &output),
            number(&real, &integral(re)),
            number(&real, &integral(im)),
        ) {
            if !close(a, g, 1e-9) || !close(b, h, 1e-9) {
                return Verdict::Wrong(format!(
                    "the integral on [{lo}, {hi}] is `{output}` = {a} + {b} i, but those of the parts are {g} and {h}"
                ));
            }
            checked += 1;
        }
    }
    if checked > 0 {
        Verdict::Pass
    } else {
        Verdict::Skip("nothing evaluated".to_owned())
    }
}

/// Check the principal logarithm and powers of the constant `a + b i` (`a; b`) against its `f64` polar form.
fn principal(input: &str) -> Verdict {
    let parts: Vec<_> = input.split(';').map(str::trim).collect();
    let real = Environment::new();
    let (Some(a), Some(b)) = (number(&real, parts[0]), number(&real, parts[1])) else {
        return Verdict::Wrong(format!("`{input}` isn't a pair of numbers"));
    };
    let z = format!("({}) + ({})*i", parts[0], parts[1]);
    let (modulus, theta) = (a.hypot(b), b.atan2(a));
    let cbrt = modulus.cbrt();
    for (expr, (re, im)) in [
        (format!("ln({z})"), (modulus.ln(), theta)),
        (format!("approx(ln({z}))"), (modulus.ln(), theta)),
        (
            format!("re(ln({z})) + i*im(ln({z}))"),
            (modulus.ln(), theta),
        ),
        (format!("approx(exp(ln({z})))"), (a, b)),
        (
            format!("approx(({z})^(1/3))"),
            (cbrt * (theta / 3.).cos(), cbrt * (theta / 3.).sin()),
        ),
        (format!("approx(abs(exp({z})))"), (a.exp(), 0.)),
    ] {
        let output = match eval_in(SetChoice::C, &mut Environment::new(), &expr) {
            Ok(output) => output,
            Err(e) => return Verdict::Wrong(format!("`{expr}`: {e}")),
        };
        let Some((u, v)) = split(&real, &output) else {
            return Verdict::Wrong(format!("`{expr}` = `{output}` isn't evaluated"));
        };
        if !close(u, re, 1e-9) || !close(v, im, 1e-9) {
            return Verdict::Wrong(format!(
                "`{expr}` = `{output}` = {u} + {v} i, expected {re} + {im} i"
            ));
        }
    }
    Verdict::Pass
}

/// An environment of `R` where `x := x0`.
fn env_with_x(x0: &str) -> Environment {
    let mut env = Environment::new();
    eval(&mut env, &format!("x := {x0}")).expect("a rational point");
    env
}

#[test]
fn oracle_reads_complex_results() {
    let env = Environment::new();
    let (a, b) = split(&env, "sin(1)-i*cos(1)+i").unwrap();
    assert!(close(a, 1f64.sin(), 1e-12) && close(b, 1. - 1f64.cos(), 1e-12));
    // Not affine in `i`
    assert!(split(&env, "1/(2*i + 1)").is_none());
    assert!(matches!(gaussian("(1 + 2*i)*(3 - i); 5; 5"), Verdict::Pass));
    assert!(matches!(
        gaussian("(1 + 2*i)*(3 - i); 5; 4"),
        Verdict::Wrong(_)
    ));
}

#[test]
fn gaussian_rationals() {
    check_all(
        "gaussian rationals",
        &[
            "(1 + 2*i)*(3 - i); 5; 5",
            "(1 + i)/(1 - i); 0; 1",
            "i^2; -1; 0",
            "(2 + i)^3; 2; 11",
            "1/(3 + 4*i); 3/25; -4/25",
            "(1/2 - i/3)*(4 + 6*i); 4; 5/3",
        ],
        gaussian,
    );
}

#[test]
fn complex_functions() {
    check_all(
        "complex functions",
        &[
            "exp(i*x); cos(x); sin(x)",
            "exp((1 + 2*i)*x); exp(x)*cos(2*x); exp(x)*sin(2*x)",
            "x*exp(-i*x); x*cos(x); -x*sin(x)",
            "(2 + i)*sin(x); 2*sin(x); sin(x)",
            "conj(exp(i*x)); cos(x); -sin(x)",
            "exp(i*x)*exp(i*x); cos(2*x); sin(2*x)",
            "(x + i)^2; x^2 - 1; 2*x",
            "ln(x + i); ln(x^2 + 1)/2; pi/2 - atan(x)",
            "ln(x - 2*i); ln(x^2 + 4)/2; atan(x/2) - pi/2",
        ],
        calculus,
    );
}

#[test]
fn principal_values() {
    check_all(
        "principal values",
        &[
            "1; 1",
            "-1; 0",
            "0; 1",
            "0; -1",
            "-3; 4",
            "-1; -1",
            "2; -5",
            "-1/2; 1/3",
            "7; 0",
        ],
        principal,
    );
}

#[test]
#[ignore = "fuzz: random Gaussian rational expressions, run with --ignored"]
fn fuzz_gaussian() {
    fuzz(
        "fuzz gaussian",
        150,
        |rng| {
            let (expr, value) = gaussian_expr(rng, 3);
            format!("{expr}; {}; {}", value.0, value.1)
        },
        gaussian,
    );
}

#[test]
#[ignore = "fuzz: random complex functions, run with --ignored"]
fn fuzz_complex_functions() {
    fuzz(
        "fuzz complex functions",
        100,
        |rng| {
            let p = parts(rng, 2);
            format!("{}; {}; {}", p.complex, p.re, p.im)
        },
        calculus,
    );
}

#[test]
fn bug_joining_large_parts_hangs() {
    // `parts::join` simplified `{$u + i v$}` whatever its size, which didn't finish with several exponentials
    assert_pass(
        "exp((2 - 2*i)*x) + (3 + 3*i) + exp((-2 - 3*i)*x); exp(2*x)*cos(2*x) + 3 + exp(-2*x)*cos(3*x); \
         -exp(2*x)*sin(2*x) + 3 - exp(-2*x)*sin(3*x)",
        Duration::from_secs(60),
        calculus,
    );
}
