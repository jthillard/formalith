//! Sums and products with `sum` and `product`: closed forms, Gosper's algorithm, infinite sums and products.
use formalith::{dynamic::SetChoice, field::real::R, parse};

use crate::common::{eval_statements, line, typst};

fn eval(input: &str) -> String {
    line(&parse!(input, R))
}

/// Check that `sum(f, k, a, n)` has a closed form, equal to the sum computed term by term for a few `n`.
fn check(f: &str, a: i64) {
    let closed = eval(&format!("sum({f}, k, {a}, n)"));
    assert!(!closed.contains("sum"), "sum({f}) not evaluated: {closed}");
    for n in a..a + 6 {
        let difference = eval_statements(
            SetChoice::R,
            &[
                &format!("c(n) := {closed}"),
                &format!("simplify(c({n}) - sum({f}, k, {a}, {n}))"),
            ],
            false,
        );
        assert_eq!(
            difference,
            Ok("0".to_string()),
            "sum({f}) = {closed} at n = {n}"
        );
    }
}

#[test]
fn polynomial_sums() {
    assert_eq!(eval("sum(k, k, 1, n)"), eval("n*(n+1)/2"));
    assert_eq!(eval("sum(k^2, k, 1, n)"), eval("n*(n+1)*(2*n+1)/6"));
    assert_eq!(eval("sum(k^3, k, 1, n)"), eval("n^2*(n+1)^2/4"));
    assert_eq!(eval("sum(c, k, 1, n)"), eval("c*n"));
    for f in [
        "k^5",
        "a*k^2+b",
        "(k+1)^3-2*k",
        "binomial(k, 2)",
        "binomial(k+3, 4)",
    ] {
        check(f, 0);
    }
}

#[test]
fn geometric_sums() {
    assert_eq!(eval("sum(2^k, k, 0, n)"), eval("2^(n+1)-1"));
    assert_eq!(eval("sum(1/2^k, k, 0, oo)"), "2");
    assert_eq!(eval("sum((-1/2)^k, k, 0, oo)"), "2/3");
    assert_eq!(eval("sum(exp(-k), k, 0, oo)"), eval("-1/(exp(-1)-1)"));
    for f in [
        "3^k",
        "k*2^k",
        "k^2*3^k",
        "r^k",
        "x*r^k",
        "(-1)^k*k",
        "2^(2*k+1)",
    ] {
        check(f, 0);
    }
}

#[test]
fn gosper() {
    assert_eq!(
        eval("sum(k*factorial(k), k, 0, n)"),
        eval("factorial(n+1)-1")
    );
    assert_eq!(eval("sum(1/(k*(k+1)), k, 1, n)"), eval("n/(n+1)"));
    assert_eq!(
        eval("sum(k/factorial(k+1), k, 0, n)"),
        eval("1 - 1/factorial(n+1)")
    );
    for f in [
        "1/(k*(k+1)*(k+2))",
        "(2*k+1)/(k^2*(k+1)^2)",
        "k*factorial(k)",
        "(-1)^k*binomial(5, k)",
        "binomial(2*k, k)/4^k*(1/(2*k-1))",
        "2^k/factorial(k+2)*k",
    ] {
        check(f, 1);
    }
    // Not Gosper-summable
    assert!(eval("sum(binomial(n, k), k, 0, m)").starts_with("sum("));
    assert!(eval("sum(1/factorial(k), k, 0, n)").starts_with("sum("));
}

#[test]
fn rational_sums() {
    assert_eq!(
        eval("sum(1/k, k, 1, n)"),
        eval("polygamma(0, n+1) + euler_gamma")
    );
    assert_eq!(
        eval("sum(1/k^2, k, 1, n)"),
        eval("pi^2/6 - polygamma(1, n+1)")
    );
    check("1/k^2 + k", 1);
}

#[test]
fn alternating_series() {
    assert_eq!(eval("sum((-1)^k/k, k, 1, oo)"), eval("-ln(2)"));
    assert_eq!(eval("sum((-1)^(k+1)/k, k, 1, oo)"), eval("ln(2)"));
    assert_eq!(eval("sum((-1)^k/k, k, 2, oo)"), eval("-(ln(2) - 1)"));
    assert_eq!(eval("sum((-1)^k/k^2, k, 1, oo)"), eval("-pi^2/12"));
    // Leibniz's series, with Gauss's digamma theorem
    assert_eq!(eval("sum((-1)^k/(2*k+1), k, 0, oo)"), eval("pi/4"));
    assert_eq!(
        eval("sum((-1)^k/(3*k+1), k, 0, oo)"),
        eval("ln(2)/3 + pi*sqrt(3)/9")
    );
    // Terms not tending to 0
    assert_eq!(eval("sum((-1)^k*k, k, 1, oo)"), "undefined");
}

#[test]
fn logarithmic_series() {
    assert_eq!(eval("sum((1/2)^k/k, k, 1, oo)"), eval("ln(2)"));
    assert_eq!(eval("sum(2^(-k)/k, k, 1, oo)"), eval("ln(2)"));
    assert_eq!(eval("sum((-1/3)^k/(k+1), k, 0, oo)"), eval("3*ln(4/3)"));
    assert_eq!(eval("sum(2^k/k, k, 1, oo)"), "+oo");
    assert_eq!(eval("sum((-2)^k/k, k, 1, oo)"), "undefined");
    assert_eq!(
        eval("sum(x^k/k, k, 1, oo)"),
        eval("piecewise(x < -1, undefined, x < 1, -ln(1 - x), oo)")
    );
}

#[test]
fn digamma_at_rationals() {
    assert_eq!(eval("digamma(1/4)"), eval("-euler_gamma - pi/2 - 3*ln(2)"));
    assert_eq!(eval("digamma(3/4)"), eval("-euler_gamma + pi/2 - 3*ln(2)"));
    assert_eq!(
        eval("digamma(2/3)"),
        eval("-euler_gamma + pi*sqrt(3)/6 - 3/2*ln(3)")
    );
    assert_eq!(
        eval("digamma(1/6)"),
        eval("-euler_gamma - pi*sqrt(3)/2 - 2*ln(2) - 3/2*ln(3)")
    );
    assert_eq!(eval("digamma(7/4)"), eval("digamma(3/4) + 4/3"));
    assert_eq!(eval("digamma(-1/3)"), eval("digamma(2/3) + 3"));
    assert!(
        eval("digamma(1/5)").starts_with("polygamma("),
        "{}",
        eval("digamma(1/5)")
    );
}

#[test]
fn infinite_sums() {
    assert_eq!(eval("sum(1/k^2, k, 1, oo)"), eval("pi^2/6"));
    assert_eq!(eval("sum(1/k^2, k, 2, oo)"), eval("pi^2/6 - 1"));
    assert_eq!(eval("sum(1/(k+1/2)^2, k, 0, oo)"), eval("pi^2/2"));
    assert_eq!(eval("sum(1/k^3, k, 1, oo)"), eval("zeta(3)"));
    assert_eq!(eval("sum(1/(k^2-1), k, 2, oo)"), "3/4");
    assert_eq!(eval("sum(1/(k*(k+1)), k, 1, oo)"), "1");
    assert_eq!(eval("sum(k/factorial(k+1), k, 0, oo)"), "1");
    assert_eq!(eval("sum(1/k, k, 1, oo)"), "+oo");
    assert_eq!(eval("sum(-k, k, 0, oo)"), "-oo");
    assert_eq!(eval("sum(k, k, -oo, 0)"), "-oo");
    assert_eq!(eval("sum(1, k, 0, oo)"), "+oo");
    assert_eq!(eval("sum((-1)^k, k, 0, oo)"), "undefined");
    // Powers of zero: only the term `{$0^0 = 1$}`
    assert_eq!(eval("sum(0^k, k, 0, oo)"), "1");
    assert_eq!(eval("sum(0^k, k, 1, oo)"), "0");
    assert_eq!(eval("sum(x*0^(k - 2), k, 2, oo)"), "x");
    assert_eq!(eval("sum(0^(2*k - 3), k, 2, oo)"), "0");
    // Divisions by zero
    assert!(eval("sum(0^(k - 2), k, 0, oo)").starts_with("sum("));
    assert!(eval("sum(0^(-k), k, 0, oo)").starts_with("sum("));
    // Every case of the geometric series, `{$x <= -1$}` oscillating and `{$x = 0$}` merged
    assert_eq!(
        eval("sum(x^k, k, 0, oo)"),
        eval("piecewise(x <= -1, undefined, x < 1, -1/(x - 1), oo)")
    );
    assert_eq!(
        eval_statements(
            SetChoice::R,
            &["assume(x < -1)", "sum(x^k/(x - 1), k, 0, oo)"],
            false
        ),
        Ok("undefined".to_string())
    );
    assert_eq!(
        eval_statements(
            SetChoice::R,
            &["assume(x > 1)", "sum(-x^k/(x + 1), k, 0, oo)"],
            false
        ),
        Ok("-∞".to_string())
    );
    // Known series
    assert_eq!(eval("sum(1/k^s, k, 1, oo)"), eval("zeta(s)"));
    assert_eq!(eval("sum(x^k/factorial(k), k, 0, oo)"), eval("exp(x)"));
    assert_eq!(
        eval("sum(x^k/factorial(k), k, 2, oo)"),
        eval("exp(x) - x - 1")
    );
    assert_eq!(eval("sum(1/factorial(k), k, 0, oo)"), eval("exp(1)"));
}

#[test]
fn concrete_bounds() {
    assert_eq!(eval("sum(1/k, k, 1, 10)"), "7381/2520");
    assert_eq!(eval("sum(k, k, 5, 2)"), "0");
    assert_eq!(eval("sum(k^2, k, 1, 1000)"), "333833500");
    assert_eq!(eval("sum(sin(k), k, 1, 2)"), eval("sin(1) + sin(2)"));
    assert_eq!(eval("product(k, k, 1, 5)"), "120");
    assert_eq!(eval("product(k, k, 3, 1)"), "1");
}

#[test]
fn products() {
    assert_eq!(eval("product(k, k, 1, n)"), eval("factorial(n)"));
    assert_eq!(eval("product((k+1)/k, k, 1, n)"), eval("n+1"));
    assert_eq!(eval("product(k/(k+2), k, 1, n)"), eval("2/(n^2+3*n+2)"));
    assert_eq!(eval("product(2^k, k, 1, n)"), eval("2^(n/2+n^2/2)"));
    assert_eq!(eval("product(c, k, 1, n)"), eval("c^n"));
    // Wallis product
    assert_eq!(eval("product(4*k^2/(4*k^2-1), k, 1, oo)"), eval("pi/2"));
    assert_eq!(eval("product(1+1/k, k, 1, oo)"), "+oo");
    assert_eq!(eval("product(1-1/k^2, k, 2, oo)"), "1/2");
    assert!(eval("product(k^2+1, k, 1, n)").starts_with("product("));
}

#[test]
fn printing() {
    assert_eq!(
        typst(&parse!("sum(k^k, k, 1, n)", R)),
        "sum_(k = 1)^(n) k^k"
    );
    assert_eq!(
        // One symbol: the order of the terms of `x + k` depends on the symbol the process interned first
        typst(&parse!("product(k^2 + 1, k, 1, n)", R)),
        "product_(k = 1)^(n) (k^2+1)"
    );
}

/// Check that `sum(f, k, a, b)`, `f` and `b` depending on `n`, has a closed form, equal to the sum computed term
/// by term for a few `n`.
fn check_definite(f: &str, a: i64, b: &str, from: i64) -> String {
    let closed = eval(&format!("sum({f}, k, {a}, {b})"));
    assert!(
        !closed.contains("sum"),
        "sum({f}, k, {a}, {b}) not evaluated: {closed}"
    );
    for n in from..from + 6 {
        let difference = eval_statements(
            SetChoice::R,
            &[
                &format!("c(n) := {closed}"),
                &format!("simplify(c({n}) - subs(sum({f}, k, {a}, {b}), n, {n}))"),
            ],
            false,
        );
        assert_eq!(
            difference,
            Ok("0".to_string()),
            "sum({f}, k, {a}, {b}) = {closed} at n = {n}"
        );
    }
    closed
}

#[test]
fn zeilberger() {
    assert_eq!(eval("sum(binomial(n, k), k, 0, n)"), eval("2^n"));
    assert_eq!(eval("sum(k*binomial(n, k), k, 0, n)"), eval("n*2^n/2"));
    assert_eq!(
        eval("sum(binomial(n, k)^2, k, 0, n)"),
        eval("binomial(2*n, n)")
    );
    assert_eq!(eval("sum(binomial(n, k)*x^k, k, 0, n)"), eval("(x+1)^n"));
    assert_eq!(eval("sum((-1)^k*binomial(n, k), k, 0, n)"), "0");
    assert_eq!(eval("sum(binomial(n, k), k, 0, n-1)"), eval("2^n - 1"));
    assert_eq!(eval("sum(binomial(2*n, k), k, 0, 2*n)"), eval("4^n"));
    // Vandermonde's identity, with a parameter
    assert_eq!(
        eval("sum(binomial(n, k)*binomial(m, n - k), k, 0, n)"),
        eval("binomial(m + n, n)")
    );
    // The closed form from `{$n = 1$}`, the certificate having a pole at 0
    assert_eq!(
        eval("sum(binomial(2*n, 2*k), k, 0, n)"),
        eval("piecewise(n = 0, 1, 4^n/2)")
    );
    assert_eq!(
        eval("sum(binomial(n, k)/((k + 2)*(k + 3)), k, 0, n)"),
        eval("(4*n*2^n - 4*2^n + n + 5)/((n + 1)*(n + 2)*(n + 3))")
    );
    // No hypergeometric closed form: Franel numbers, central Delannoy numbers
    assert!(eval("sum(binomial(n, k)^3, k, 0, n)").starts_with("sum("));
    assert!(eval("sum(binomial(n, k)*binomial(n + k, k), k, 0, n)").starts_with("sum("));
    for (f, a, b, from) in [
        ("binomial(n, k)", 0, "n", 0),
        ("k*binomial(n, k)", 0, "n", 0),
        ("k^2*binomial(n, k)", 0, "n", 0),
        ("binomial(n, k)^2", 0, "n", 0),
        ("binomial(n, k)/(k + 1)", 0, "n", 0),
        ("binomial(n, k)*binomial(n, n - k)", 0, "n", 0),
        ("binomial(n, k)*2^k", 0, "n", 0),
        ("binomial(n, k)", 1, "n", 1),
        ("binomial(n, k)", 0, "n - 1", 1),
        ("binomial(2*n, k)", 0, "2*n", 0),
        ("binomial(n, k)*binomial(2*k, k)*(-1/4)^k", 0, "n", 0),
        ("binomial(n, k)*binomial(n, k + 1)", 0, "n", 0),
        ("binomial(n + k, k)/2^k", 0, "n", 0),
        ("binomial(2*n, 2*k)", 0, "n", 0),
        ("binomial(n, k)/((k + 2)*(k + 3))", 0, "n", 0),
    ] {
        check_definite(f, a, b, from);
    }
}
