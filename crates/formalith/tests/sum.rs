//! Sums and products with `sum` and `product`: closed forms, Gosper's algorithm, infinite sums and products.
use formalith::{dynamic::SetChoice, field::real::R, parse};

mod common;
use common::{eval_statements, line, typst};

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
fn infinite_sums() {
    assert_eq!(eval("sum(1/k^2, k, 1, oo)"), eval("pi^2/6"));
    assert_eq!(eval("sum(1/k^2, k, 2, oo)"), eval("pi^2/6 - 1"));
    assert_eq!(eval("sum(1/(k+1/2)^2, k, 0, oo)"), eval("pi^2/2"));
    assert_eq!(eval("sum(1/k^3, k, 1, oo)"), eval("zeta(3)"));
    assert_eq!(eval("sum(1/(k^2-1), k, 2, oo)"), "3/4");
    assert_eq!(eval("sum(1/(k*(k+1)), k, 1, oo)"), "1");
    assert_eq!(eval("sum(k/factorial(k+1), k, 0, oo)"), "1");
    assert_eq!(eval("sum(1/k, k, 1, oo)"), "oo");
    assert_eq!(eval("sum(-k, k, 0, oo)"), "-oo");
    assert_eq!(eval("sum(k, k, -oo, 0)"), "-oo");
    assert_eq!(eval("sum(1, k, 0, oo)"), "oo");
    assert_eq!(eval("sum((-1)^k, k, 0, oo)"), "undefined");
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
    assert_eq!(eval("product(1+1/k, k, 1, oo)"), "oo");
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
        typst(&parse!("product(x + k, k, 1, oo)", R)),
        "product_(k = 1)^(oo) (k+x)"
    );
}
