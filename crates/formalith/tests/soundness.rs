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
