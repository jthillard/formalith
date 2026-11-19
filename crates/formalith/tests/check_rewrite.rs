//! Rewriting builtins checked against their definition: `simplify`, `expand`, `factor` and `apart` give a term
//! equivalent to their argument (numerically, at random points). Also core arithmetic found broken that way.
mod common;

use common::{
    harness::{Verdict, assert_pass, case_rng, check_all, fuzz},
    numeric::{Domain, env_with, equivalent, eval, symbols},
    random,
    rng::Rng,
};
use std::time::Duration;

/// Check `op(f)` against `f` for `input` = `op; f`.
fn rewrite(input: &str) -> Verdict {
    let (op, f) = input.split_once(';').unwrap();
    let (op, f) = (op.trim(), f.trim());
    let mut env = env_with(&[]);
    let result = match eval(&mut env, &format!("{op}({f})")) {
        Ok(res) => res,
        Err(e) => return Verdict::Skip(e),
    };
    let names = symbols(f);
    let vars: Vec<_> = names.iter().map(|n| (n.as_str(), Domain::Any)).collect();
    let mut rng = case_rng(input);
    match equivalent(&env, f, &result, &vars, &mut rng).into() {
        Verdict::Wrong(why) => Verdict::Wrong(format!("{op}({f}) = {result}: {why}")),
        verdict => verdict,
    }
}

/// Check that `f` evaluates to something equivalent to itself evaluated in `R` term by term: the expression is
/// normalized by the parser, so this compares the normalization with a numerical evaluation of the source.
fn normalization(f: &str) -> Verdict {
    let mut env = env_with(&[]);
    let normalized = match eval(&mut env, f) {
        Ok(res) => res,
        Err(e) => return Verdict::Skip(e),
    };
    // The source, evaluated at points through a definition, is normalized too, so compare with approx of the
    // source with every variable replaced by a value before parsing (`Function` substitutes before normalizing)
    let names = symbols(f);
    let vars: Vec<_> = names.iter().map(|n| (n.as_str(), Domain::Any)).collect();
    let mut rng = case_rng(f);
    match equivalent(&env, f, &normalized, &vars, &mut rng).into() {
        Verdict::Wrong(why) => Verdict::Wrong(format!("{f} = {normalized}: {why}")),
        verdict => verdict,
    }
}

#[test]
fn rewrites() {
    check_all(
        "rewrites",
        &[
            "expand; (x + y)^5",
            "expand; (x - 1)*(x^2 + x + 1)*(y + 2)",
            "expand; sin(x + y)",
            "expand; cos(2*x)*sin(x - y)",
            "simplify; (x^2 - 1)/(x - 1)",
            "simplify; sin(x)^2 + cos(x)^2 + x",
            "simplify; exp(2*ln(x))",
            "simplify; sinh(x)/cosh(x)",
            "simplify; (exp(x) - exp(-x))/2",
            "simplify; ln(x^2)/ln(x)",
            "simplify; 1/(1/x + 1/y)",
            "simplify; sin(2*x)/sin(x)",
            "simplify; sqrt(x^2 + 2*x + 1)",
            "factor; x^4 - 1",
            "factor; x^2*y - y^3",
            "factor; 6*x^2 + 7*x - 3",
            "factor; x^6 - y^6",
            "apart; (x + 1)/(x^2 - 5*x + 6)",
            "apart; 1/(x^2*(x + 1))",
            "apart; (x^3 + 1)/(x^2 + 1)",
            "apart; 1/((x - 1)^2*(x^2 + 1))",
        ],
        rewrite,
    );
}

/// A random polynomial expression in factored form, to be factored again after expansion.
fn product(rng: &mut Rng) -> String {
    let count = rng.range(2, 3);
    let factors: Vec<_> = (0..count)
        .map(|_| random::polynomial(rng, &["x", "y"], 2, 2))
        .collect();
    factors.join("*")
}

#[test]
#[ignore = "fuzz: random expansions, run with --ignored"]
fn fuzz_expand() {
    fuzz(
        "fuzz expand",
        60,
        |rng| format!("expand; {}", random::expr(rng, &["x", "y"], 3)),
        rewrite,
    );
}

#[test]
#[ignore = "fuzz: random simplifications, run with --ignored"]
fn fuzz_simplify() {
    fuzz(
        "fuzz simplify",
        60,
        |rng| {
            let f = match rng.below(4) {
                0 => random::rational_function(rng, &["x", "y"]),
                1 => random::trig_poly(rng),
                2 => random::exp_poly(rng),
                _ => random::expr(rng, &["x", "y"], 3),
            };
            format!("simplify; {f}")
        },
        rewrite,
    );
}

#[test]
#[ignore = "fuzz: random factorizations, run with --ignored"]
fn fuzz_factor() {
    fuzz(
        "fuzz factor",
        60,
        |rng| {
            let p = product(rng);
            format!("factor; expand({p})")
        },
        rewrite,
    );
}

#[test]
#[ignore = "fuzz: random partial fractions, run with --ignored"]
fn fuzz_apart() {
    fuzz(
        "fuzz apart",
        60,
        |rng| {
            let p = random::polynomial(rng, &["x"], 3, 3);
            let count = rng.range(1, 3) as usize;
            let q = random::linear_factors(rng, "x", count);
            let extra = if rng.chance(0.4) {
                format!("*(x^2 + {})", rng.range(1, 3))
            } else {
                String::new()
            };
            format!("apart; {p}/({q}{extra})")
        },
        rewrite,
    );
}

#[test]
#[ignore = "fuzz: normalization of random expressions, run with --ignored"]
fn fuzz_normalization() {
    fuzz(
        "fuzz normalization",
        100,
        |rng| random::expr(rng, &["x", "y"], 4),
        normalization,
    );
}

/// A product of a constant and powers sharing bases, like `3/2*x^(1/3)*y*x^(-1/3)`.
fn powers(rng: &mut Rng) -> String {
    let bases = ["x", "y", "pi", "(x + 1)", "e", "3"];
    let exponents = [
        "1", "2", "-1", "-2", "1/2", "-1/2", "1/3", "-1/3", "3/2", "-3/2",
    ];
    let mut factors = vec![random::constant(rng)];
    for _ in 0..rng.range(2, 4) {
        let base = rng.pick(&bases);
        factors.push(format!("{base}^({})", rng.pick(&exponents)));
    }
    factors.join("*")
}

#[test]
#[ignore = "fuzz: products of powers, run with --ignored"]
fn fuzz_powers() {
    fuzz("fuzz powers", 100, powers, normalization);
}

fn regression(input: &str, check: fn(&str) -> Verdict) {
    assert_pass(input, Duration::from_secs(60), check);
}

#[test]
fn bug_coefficient_times_cancelling_powers_is_zero() {
    let mut env = env_with(&[]);
    // `2*x*x^(-1)` is right, but not other exponents; also `(1/2)*sqrt(pi)/sqrt(pi)` and `pi^(-1/2)*gamma(3/2)`
    for f in [
        "2*x^2*x^(-2)",
        "2*sqrt(x)/sqrt(x)",
        "(1/2)*pi^(1/3)*pi^(-1/3)",
        "pi^(-1/2)*gamma(3/2)",
    ] {
        let res = eval(&mut env, f).unwrap();
        assert_ne!(res, "0", "{f}");
    }
}

#[test]
fn bug_zero_over_zero_panics() {
    let mut env = env_with(&[]);
    for f in ["0/0", "0*(1/(2-2))", "simplify(x + 0/0)"] {
        assert_eq!(eval(&mut env, f).as_deref(), Ok("undefined"), "{f}");
    }
}

#[test]
fn bug_zero_times_division_by_zero() {
    let mut env = env_with(&[]);
    for f in ["0*(x/0)", "x/0 - x/0"] {
        assert_ne!(eval(&mut env, f).ok().as_deref(), Some("0"), "{f}");
    }
}

#[test]
fn bug_simplify_square_drops_constant() {
    // Likely `bug_coefficient_times_cancelling_powers_is_zero` on the `4*x^2*x^-2` of the common denominator
    regression("simplify; (2 + 1/x)^2", rewrite);
}
