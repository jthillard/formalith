//! Regressions for results that were wrong rather than unevaluated: rules applied without their side conditions,
//! and exact decisions (zero tests, signs, equal bounds) taken from floating point approximations.
use formalith::{dynamic::SetChoice, parser::environment::Environment, printer::PrintOptions};

/// The result of the last statement evaluated in `set` with shared definitions, on one line.
fn eval_in(set: &str, statements: &[&str]) -> String {
    let set = set.parse::<SetChoice>().unwrap();
    let mut env = Environment::new();
    let mut result = String::new();
    for statement in statements {
        result = set.evaluate(statement, &mut env).map_or_else(
            |err| format!("error: {err}"),
            |result| result.print(PrintOptions::plain()),
        );
    }
    result
}

/// The result of `statement` in `{$RR$}`.
fn eval_r(statement: &str) -> String {
    eval_in("R", &[statement])
}

#[test]
fn expand_powers_of_products() {
    // `{$(x y)^(1/2) = 1$}` for `{$x = y = -1$}`, while `{$x^(1/2) y^(1/2)$}` would be `{$-1$}`
    assert_eq!(eval_r("expand((x*y)^(1/2))"), "(x*y)^(1/2)");
    assert_eq!(eval_r("expand((4*x*y)^(1/2))"), "2*((x*y)^(1/2))");
    assert_eq!(eval_r("expand((x^2*y)^(1/2))"), "(y^(1/2))*abs(x)");
    // Real odd roots are multiplicative
    assert_eq!(eval_r("expand((x*y)^(1/3))"), "(x^(1/3))*(y^(1/3))");
    assert_eq!(
        eval_in("R", &["assume(x > 0, y > 0)", "expand((x*y)^(1/2))"]),
        "(x^(1/2))*(y^(1/2))"
    );
}

#[test]
fn signs_of_radicals_in_roots() {
    // The discriminant `{$10^20 sqrt(2) - 141421356237309504881$}` is about `{$-0.83$}`, positive in floats
    assert_eq!(
        eval_r("solve(x^2 + 10^10*2^(1/4)*x + 141421356237309504881/4 = 0, x)"),
        "no solution"
    );
}

#[test]
fn constants_indistinguishable_from_zero() {
    // `{$sin(10^(-2000))$}` is positive, but zero at the maximum precision of approximations
    assert!(eval_r("sin(10^(-2000)) > 0").starts_with("error"));
    assert_eq!(eval_r("sin(pi) > 0"), "no solution");
}

#[test]
fn close_roots_of_inequalities() {
    // Roots within the relative accuracy of approximations aren't merged
    let bound =
        "10000000000000000000000000000000000000001/10000000000000000000000000000000000000000";
    assert_eq!(
        eval_r("(x-1)*(x-1-10^(-40)) < 0"),
        format!("x ∈ (1, {bound})")
    );
    assert_eq!(
        eval_r("(x-1)*(x-1-10^(-40)) <= 0"),
        format!("x ∈ [1, {bound}]")
    );
    assert!(eval_r("(x-sqrt(2))*(x-sqrt(2)-10^(-50)) < 0").starts_with("error"));
}
