//! Global extrema with `argmin` and `argmax`.
mod common;

/// Evaluate `statements` in `R`, printed as Typst so that the output doesn't depend on colors.
fn eval(statements: &[&str]) -> Result<String, String> {
    common::eval_statements("R".parse().unwrap(), statements, true)
}

fn argmin(statement: &str) -> Result<String, String> {
    eval(&[statement])
}

/// The solutions of `equations`, printed like those of `argmin`, so that terms are ordered like in the result.
fn solved(equations: &str) -> Result<String, String> {
    eval(&[&format!("solve({equations})")])
}

/// The result when the extremum isn't reached.
fn none() -> Result<String, String> {
    Ok("\"no solution\"".to_owned())
}

#[test]
fn polynomials() {
    assert_eq!(argmin("argmin(x^2 - 2*x, x)"), solved("x = 1, x"));
    assert_eq!(argmin("argmin(x^4 - 2*x^2, x)"), solved("x^2 = 1, x"));
    assert_eq!(argmin("argmax(x - x^2, x)"), solved("x = 1/2, x"));
    // Every symbol of the function by default
    assert_eq!(argmin("argmin(x^2 - 2*x)"), solved("x = 1, x"));
    assert_eq!(argmin("argmin(x^3, x)"), none());
    assert_eq!(argmin("argmin(x, x)"), none());
    assert_eq!(argmin("argmax(x^2, x)"), none());
}

#[test]
fn intervals() {
    assert_eq!(argmin("argmin(x^3 - 3*x, x, -3, 3)"), solved("x = -3, x"));
    assert_eq!(argmin("argmax(x^3 - 3*x, x, -3, 3)"), solved("x = 3, x"));
    assert_eq!(
        argmin("argmin(x^3 - 3*x, x, -2, 3)"),
        solved("x^2 + x - 2 = 0, x")
    );
    assert_eq!(argmin("argmin(x^2, x, 1, oo)"), solved("x = 1, x"));
    assert_eq!(argmin("argmax(sin(x), x, 0, 4)"), solved("x = pi/2, x"));
    assert_eq!(argmin("argmin(1/x, x, 1, 2)"), solved("x = 2, x"));
    assert!(argmin("argmin(x^2, x, 2, 1)").is_err());
}

#[test]
fn transcendental() {
    assert_eq!(argmin("argmax(x*exp(-x), x)"), solved("x = 1, x"));
    assert_eq!(argmin("argmin(x*ln(x), x)"), solved("x = exp(-1), x"));
    assert_eq!(argmin("argmin(exp(x), x)"), none());
    assert_eq!(argmin("argmin(x - 2*sin(x), x)"), none());
    // Periodic minimizers
    assert_eq!(argmin("argmin(cos(x), x)"), solved("cos(x) = -1, x"));
    assert_eq!(argmin("argmax(sin(x), x)"), solved("sin(x) = 1, x"));
}

#[test]
fn domains_and_singularities() {
    assert_eq!(argmin("argmin(sqrt(x), x)"), solved("x = 0, x"));
    assert_eq!(argmin("argmin(x^2 + 1/x^2, x)"), solved("x^2 = 1, x"));
    assert_eq!(argmin("argmin(1/x, x)"), none());
    assert_eq!(argmin("argmin(1/(x^2 - 1), x)"), none());
}

#[test]
fn absolute_values() {
    assert_eq!(argmin("argmin(abs(x - 2), x)"), solved("x = 2, x"));
    assert_eq!(argmin("argmin(abs(x^2 - 1) + x, x)"), solved("x = -1, x"));
    assert_eq!(argmin("argmax(abs(x) - x^2, x)"), solved("x^2 = 1/4, x"));
    assert_eq!(
        argmin("argmax(abs(x - 1) + abs(x + 1), x, -2, 3)"),
        solved("x = 3, x")
    );
    // Constant on `{$[-1, 1]$}`
    assert!(argmin("argmin(abs(x - 1) + abs(x + 1), x)").is_err());
}

#[test]
fn parameters() {
    assert_eq!(
        eval(&["assume(a > 0)", "argmin(a*x^2 + b*x, x)"]),
        eval(&["solve(2*a*x + b = 0, x)"])
    );
    assert_eq!(eval(&["assume(a < 0)", "argmin(a*x^2 + b*x, x)"]), none());
    // The sign of `a` is unknown
    assert!(argmin("argmin(a*x^2 + b*x, x)").is_err());
}

#[test]
fn several_variables() {
    assert_eq!(
        argmin("argmin(x^2 + y^2 - 2*x, x, y)"),
        solved("x = 1, y = 0, x, y")
    );
    assert_eq!(
        argmin("argmax(-x^2 - (y - 1)^2, x, y)"),
        solved("x = 0, y = 1, x, y")
    );
    // A line of minimizers
    assert_eq!(argmin("argmin((x - y)^2, x, y)"), solved("x = y, x, y"));
    // A local minimum only
    assert_eq!(argmin("argmin(x^3 - 3*x + y^2, x, y)"), none());
    assert_eq!(argmin("argmin(x*y, x, y)"), none());
    assert!(argmin("argmin(exp(x + y), x, y)").is_err());
    assert!(argmin("argmin(x^2 + a*y^2, x, y)").is_err());
}

#[test]
fn errors() {
    assert!(argmin("argmin(x = 1, x)").is_err());
    assert!(argmin("argmin(x^2, 2)").is_err());
    assert!(argmin("argmin(x^2, x, x)").is_err());
    assert!(argmin("argmin(x^2, pi)").is_err());
    assert!(argmin("argmin(5)").is_err());
    assert!(argmin("argmin(floor(x), x)").is_err());
}
