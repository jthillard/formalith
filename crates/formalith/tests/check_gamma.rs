//! The Gamma family checked against functional equations at random points, and exact values (at integers,
//! half-integers, even zeta arguments...) against the numerical algorithm at a point moved by `10^-25`, where no
//! exact rule applies.

use crate::common::{
    harness::{Verdict, case_rng, check_all},
    numeric::{Domain, close, env_with, equivalent, number},
};

/// Check the identity `input` = `lhs; rhs; domain of x` (`pos`, `neg`, `unit`, `w`).
fn identity(input: &str) -> Verdict {
    let parts: Vec<_> = input.split(';').map(str::trim).collect();
    let domain = match parts[2] {
        "pos" => Domain::Range(0.1, 5.0),
        "neg" => Domain::Range(-3.9, -0.1),
        "unit" => Domain::Range(0.05, 0.95),
        "w" => Domain::Range(-0.36, 5.0),
        "wm1" => Domain::Range(-0.36, -0.01),
        other => panic!("unknown domain {other}"),
    };
    let env = env_with(&[]);
    let mut rng = case_rng(input);
    equivalent(&env, parts[0], parts[1], &[("x", domain)], &mut rng).into()
}

/// Check that the exact value of `f` at `x0` agrees with the approximation of `f` at `x0 + 10^-25` (`input` is
/// `f; x0`, `f` in `x`).
fn exact_value(input: &str) -> Verdict {
    let (f, x0) = input.split_once(';').unwrap();
    let (f, x0) = (f.trim(), x0.trim());
    let env = env_with(&[]);
    let exact = f.replace('x', &format!("({x0})"));
    let moved = f.replace('x', &format!("({x0} + 1/10^25)"));
    match (number(&env, &exact), number(&env, &moved)) {
        (Some(a), Some(b)) if close(a, b, 1e-12) => Verdict::Pass,
        (Some(a), Some(b)) => Verdict::Wrong(format!("exact {exact} = {a} but near it {b}")),
        _ => Verdict::Skip(format!("{exact} doesn't evaluate")),
    }
}

#[test]
fn functional_equations() {
    check_all(
        "gamma family",
        &[
            "gamma(x + 1); x*gamma(x); pos",
            "gamma(x + 1); x*gamma(x); neg",
            "gamma(x)*gamma(1 - x); pi/sin(pi*x); unit",
            "gamma(x)*gamma(x + 1/2); 2^(1 - 2*x)*sqrt(pi)*gamma(2*x); pos",
            "factorial(x); gamma(x + 1); pos",
            "beta(x, 2*x); gamma(x)*gamma(2*x)/gamma(3*x); pos",
            "beta(x, 3); beta(3, x); pos",
            "polygamma(0, x + 1) - polygamma(0, x); 1/x; pos",
            "polygamma(1, x + 1) - polygamma(1, x); -1/x^2; pos",
            "polygamma(2, x + 1) - polygamma(2, x); 2/x^3; pos",
            "polygamma(3, x + 1) - polygamma(3, x); -6/x^4; neg",
            "digamma(1 - x) - digamma(x); pi/tan(pi*x); unit",
            "lambertw(x)*exp(lambertw(x)); x; w",
            "lambertw(x, -1)*exp(lambertw(x, -1)); x; wm1",
            "binomial(x, 2); x*(x - 1)/2; pos",
            // Euler-Maclaurin with 200 terms
            "zeta(x + 2); sum(1/k^(x + 2), k, 1, 200) + 1/((x + 1)*200^(x + 1)) - 1/(2*200^(x + 2)) + (x + 2)/(12*200^(x + 3)); pos",
        ],
        identity,
    );
}

#[test]
fn exact_values() {
    check_all(
        "exact values",
        &[
            "gamma(x); 5",
            "gamma(x); 1/2",
            "gamma(x); 7/2",
            "gamma(x); -1/2",
            "gamma(x); -5/2",
            "factorial(x); 3/2",
            "polygamma(0, x); 1",
            "polygamma(0, x); 4",
            "polygamma(0, x); 1/2",
            "polygamma(0, x); 7/2",
            "polygamma(1, x); 1",
            "polygamma(1, x); 3/2",
            "polygamma(2, x); 3",
            "polygamma(3, x); 5/2",
            "zeta(x); 2",
            "zeta(x); 4",
            "zeta(x); 6",
            "lambertw(x); 0",
            "lambertw(x); e",
            "lambertw(x); 2*exp(2)",
            "lambertw(x); -exp(-1)/2",
            "lambertw(x, -1); -2*exp(-2)",
            "lambertw(x, -1); -exp(-1)",
            "binomial(x, 3); 7/2",
            "beta(x, 1/2); 3/2",
        ],
        exact_value,
    );
}

#[test]
fn known_constants() {
    let env = env_with(&[]);
    for (a, b) in [
        ("zeta(2)", "pi^2/6"),
        ("zeta(4)", "pi^4/90"),
        ("zeta(0)", "-1/2"),
        ("zeta(-1)", "-1/12"),
        ("zeta(-3)", "1/120"),
        ("gamma(1/2)", "sqrt(pi)"),
        ("polygamma(0, 1)", "-euler_gamma"),
        ("polygamma(1, 1)", "pi^2/6"),
        ("approx(euler_gamma)", "0.5772156649015329"),
    ] {
        let (x, y) = (number(&env, a), number(&env, b));
        assert!(
            x.is_some() && y.is_some() && close(x.unwrap(), y.unwrap(), 1e-12),
            "{a} = {x:?}, {b} = {y:?}"
        );
    }
}
