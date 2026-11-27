//! Assumptions on symbols with `assume`, like `a > 0` or `n integer`.
use formalith::{
    context::assumptions::Assumptions, dynamic::SetChoice, field::real::R, parse,
    parser::environment::Environment,
};

use crate::common::{eval_statements, line};

/// Evaluate the statements in `R` with shared definitions and assumptions, returning the last result: an
/// expression on one line, or the printed statement, without trailing spaces.
fn eval(statements: &[&str]) -> String {
    let (last, first) = statements.split_last().unwrap();
    let mut env = Environment::new();
    for statement in first {
        env.eval(statement, R).unwrap();
    }
    if last.starts_with("assume") || last.starts_with("solve") {
        let res = SetChoice::R.eval(last, false, &mut env).unwrap();
        return res
            .lines()
            .map(str::trim_end)
            .collect::<Vec<_>>()
            .join("\n");
    }
    line(&parse!(last, R, &env))
}

/// `expected` parsed without assumptions, printed like [`eval`] results.
fn expr(expected: &str) -> String {
    line(&parse!(expected, R))
}

#[test]
fn assume_statements() {
    assert_eq!(
        eval(&["assume(a > 0, b != 0, n integer)"]),
        "a > 0, b != 0, n integer"
    );
    assert_eq!(eval(&["assume(0 < a)"]), "a > 0");
    assert_eq!(eval(&["assume(a >= 0, a <= 0)"]), "a = 0");
    assert_eq!(eval(&["assume(a >= 0)", "assume(a != 0)"]), "a > 0");
    assert_eq!(eval(&["assume(a > 0)", "assume(a)"]), "a > 0");
    assert_eq!(eval(&["assume(a)"]), "no assumption");
    // Outside of `assume`, a comparison is an inequality, restricted by the assumptions
    assert_eq!(eval(&["solve(a > 0)"]), "a ∈ (0, +∞)");
    assert_eq!(eval(&["assume(a < 0)", "solve(a^2 < 4)"]), "a ∈ (-2, 0)");
}

#[test]
fn assume_errors() {
    let err = |statements: &[&str]| eval_statements(SetChoice::R, statements, false).unwrap_err();
    assert!(err(&["assume(a > 0, a < 0)"]).contains("contradicts"));
    assert!(err(&["assume(a > 0)", "assume(a <= 0)"]).contains("contradicts"));
    assert!(err(&["assume(a*b > 1)"]).contains("linear relations"));
    assert!(err(&["assume(a^2 > 1)"]).contains("linear relations"));
    assert!(err(&["assume(1 > 0)"]).contains("no symbol"));
    assert!(err(&["assume(a > b, b > a)"]).contains("contradicts a > b"));
    assert!(err(&["assume(a > b, b > c, c > a)"]).contains("contradicts"));
    assert!(err(&["assume(a > b + 1)", "assume(b > 0, a < 1)"]).contains("contradicts"));
    assert!(err(&["assume(n integer, n > 1/3, n < 2/3)"]).contains("contradicts"));
    assert!(err(&["assume(pi > 0)"]).contains("constant"));
    assert!(err(&["assume(a < pi)"]).contains("constant"));
    assert!(
        eval_statements(SetChoice::C, &["assume(i > 0)"], false)
            .unwrap_err()
            .contains("constant")
    );
    // A rejected statement doesn't change the assumptions
    let mut env = Environment::new();
    env.eval("assume(a > 0)", R).unwrap();
    assert!(env.eval("assume(b > 0, a < 0)", R).is_err());
    assert_eq!(env.assumptions().to_string(), "a > 0");
}

#[test]
fn signs_of_symbols() {
    assert_eq!(eval(&["assume(x > 0)", "sqrt(x^2)"]), "x");
    assert_eq!(eval(&["assume(x < 0)", "sqrt(x^2)"]), "-x");
    assert_eq!(eval(&["sqrt(x^2)"]), "abs(x)");
    assert_eq!(eval(&["assume(x >= 0)", "abs(-2*x)"]), expr("2*x"));
    assert_eq!(eval(&["assume(a > 0)", "sign(-a)"]), "-1");
    assert_eq!(
        eval(&["assume(a > 0, b > 0)", "sqrt(a*b)"]),
        expr("sqrt(a)*sqrt(b)")
    );
    assert_eq!(
        eval(&["assume(a > 0)", "abs(a^2 + exp(x))"]),
        expr("a^2+exp(x)")
    );
}

#[test]
fn integers() {
    assert_eq!(eval(&["assume(n integer)", "sin(n*pi)"]), "0");
    assert_eq!(eval(&["assume(n integer)", "cos(n*pi)"]), expr("(-1)^n"));
    assert_eq!(eval(&["assume(n integer)", "cos(2*n*pi)"]), "1");
    assert_eq!(
        eval(&["assume(n integer)", "sin(x + 3*n*pi)"]),
        expr("(-1)^n*sin(x)")
    );
    assert_eq!(eval(&["assume(n integer)", "tan(x + n*pi)"]), "tan(x)");
    assert_eq!(eval(&["assume(n integer)", "(-1)^(2*n + 1)"]), "-1");
    assert_eq!(eval(&["assume(n integer)", "floor(n + 1)"]), expr("n+1"));
    assert_eq!(eval(&["sin(n*pi)"]), expr("sin(n*pi)"));
    assert_eq!(eval(&["floor(n)"]), "floor(n)");
}

#[test]
fn integrals() {
    assert_eq!(eval(&["assume(x > 0)", "integrate(1/x, x)"]), "ln(x)");
    assert_eq!(eval(&["integrate(1/x, x)"]), "ln(abs(x))");
    assert_eq!(
        eval(&["assume(a > 0)", "integrate(2*x/(x^2 + a), x)"]),
        expr("ln(x^2+a)")
    );
    assert_eq!(
        eval(&["assume(a > 0)", "integrate(exp(-a*x), x, 0, oo)"]),
        "a^-1"
    );
}

#[test]
fn limits() {
    assert_eq!(eval(&["assume(a > 0)", "lim(exp(a*x), x, oo)"]), "+oo");
    assert_eq!(eval(&["assume(a < 0)", "lim(exp(a*x), x, oo)"]), "0");
    assert_eq!(eval(&["assume(a > 0)", "lim(a*x, x, oo)"]), "+oo");
    assert_eq!(eval(&["assume(a < 0)", "lim(a*x, x, oo)"]), "-oo");
    assert_eq!(eval(&["lim(a*x, x, oo)"]), expr("sign(a)*oo"));
    // Split at `{$a = -1$}`, where the sign of `{$ln(-a)$}` changes
    assert_eq!(
        eval(&["assume(a < 0)", "lim(a^x, x, oo)"]),
        "piecewise(a <= -1, undefined, 0)"
    );
    assert_eq!(
        eval(&["assume(a > 1)", "lim(1/(a - 1)^n, n, oo)"]),
        "piecewise(a < 2, +oo, a = 2, 1, 0)"
    );
}

#[test]
fn solve_pruning() {
    assert_eq!(eval(&["assume(x > 0)", "solve(x^2 = 4, x)"]), "x = 2");
    assert_eq!(eval(&["assume(x < 0)", "solve(x^2 = 4, x)"]), "x = -2");
    assert_eq!(eval(&["assume(a < 0)", "solve(x^2 = a, x)"]), "no solution");
    assert_eq!(
        eval(&["assume(n integer)", "solve(2*n = 1, n)"]),
        "no solution"
    );
    assert_eq!(eval(&["solve(x^2 = 4, x)"]), "x = -2\nx = 2");
}

#[test]
fn environments_are_isolated() {
    let mut env = Environment::new();
    env.eval("assume(x > 0)", R).unwrap();
    assert_eq!(line(&parse!("sqrt(x^2)", R, &env)), "x");
    assert_eq!(line(&parse!("sqrt(x^2)", R)), "abs(x)");
    assert_eq!(line(&parse!("sqrt(x^2)", R, &Environment::new())), "abs(x)");
    env.clear();
    assert_eq!(line(&parse!("sqrt(x^2)", R, &env)), "abs(x)");
}

#[test]
fn definitions_and_assumptions() {
    // Definitions are expanded under the current assumptions
    assert_eq!(eval(&["f(t) := sqrt(t^2)", "assume(y > 0)", "f(y)"]), "y");
    let mut env = Environment::new();
    SetChoice::R.eval("assume(a > 0)", false, &mut env).unwrap();
    SetChoice::R.eval("b := 2", false, &mut env).unwrap();
    assert_eq!(
        formalith::dynamic::definitions(&env),
        "b := 2\nassume(a > 0)"
    );
    formalith::dynamic::clear_definitions(&mut env, "a").unwrap();
    assert_eq!(formalith::dynamic::definitions(&env), "b := 2");
    assert!(formalith::dynamic::clear_definitions(&mut env, "a").is_err());
}

#[test]
fn default_assumptions() {
    let mut env = Environment::with_default_assumptions(Assumptions::defaults());
    assert_eq!(line(&parse!("cos(2*n*pi)", R, &env)), "1");
    env.eval("assume(x > 0, n >= 0)", R).unwrap();
    assert_eq!(
        formalith::dynamic::definitions(&env),
        "assume(n >= 0, n integer, x > 0)"
    );
    formalith::dynamic::clear_definitions(&mut env, "n").unwrap();
    assert_ne!(line(&parse!("cos(2*n*pi)", R, &env)), "1");
    // Clearing restores the defaults, and only them
    env.clear();
    assert_eq!(env.assumptions(), &Assumptions::defaults());
    assert_eq!(line(&parse!("cos(2*n*pi)", R, &env)), "1");
    assert_eq!(line(&parse!("sqrt(x^2)", R, &env)), "abs(x)");
    assert_eq!(formalith::dynamic::definitions(&env), "");
}

#[test]
fn degree_with_symbolic_exponents() {
    assert_eq!(
        eval(&["assume(n integer, n >= 0)", "degree(x^n + x^10, x)"]),
        expr("max(n, 10)")
    );
    assert_eq!(
        eval(&["assume(n integer, n >= 0)", "degree(x^(n+1)*x^2 + x, x)"]),
        expr("n + 3")
    );
    assert_eq!(
        eval(&["assume(n integer, n >= 0)", "degree(x^n + x^(n+2), x)"]),
        expr("n + 2")
    );
    // `n` may be negative
    assert_eq!(
        eval(&["assume(n integer)", "degree(x^n, x)"]),
        expr("degree(x^n, x)")
    );
}

#[test]
fn typst_output() {
    assert_eq!(
        eval_statements(SetChoice::R, &["assume(a >= 0, n integer)"], true).unwrap(),
        "a >= 0, n in ZZ"
    );
}

#[test]
fn linear_assumptions() {
    // Bounds and relations, printed so that they parse back
    assert_eq!(eval(&["assume(1 < a)"]), "a > 1");
    assert_eq!(eval(&["assume(a > 0, a < 1)"]), "a > 0, a < 1");
    assert_eq!(eval(&["assume(n integer, n > 1/2)"]), "n >= 1, n integer");
    assert_eq!(
        eval(&["assume(n integer, n >= 0, n != 0)"]),
        "n >= 1, n integer"
    );
    assert_eq!(eval(&["assume(2*a > 2*b + 2)"]), "a > b+1");
    assert_eq!(eval(&["assume(a > b/2)"]), "2*a > b");
    assert_eq!(eval(&["assume(a + b < 3)"]), "a+b < 3");
    assert_eq!(eval(&["assume(a = 2*b)"]), "a = 2*b");
    assert_eq!(eval(&["assume(a != b)"]), "a != b");
    assert_eq!(eval(&["assume(a > b, c > 0)", "assume(b)"]), "a > b");
    assert_eq!(eval(&["assume(a > b, c > 0)", "assume(c)"]), "c > 0");
    // `:defs` gives a statement restoring them
    let mut env = Environment::new();
    env.eval("assume(a > b + 1, c <= 2*b, x >= -1/2, a != 3*c)", R)
        .unwrap();
    let defs = formalith::dynamic::definitions(&env);
    let mut again = Environment::new();
    again.eval(&defs, R).unwrap();
    assert_eq!(again.assumptions(), env.assumptions());
    // Removing a symbol removes its relations
    assert!(env.remove_assumptions("b"));
    assert_eq!(env.assumptions().to_string(), "x >= -1/2, a != 3*c");
}

#[test]
fn linear_signs() {
    assert_eq!(eval(&["assume(a > 1)", "abs(a - 1)"]), expr("a - 1"));
    assert_eq!(eval(&["assume(a > 1)", "abs(ln(a))"]), expr("ln(a)"));
    assert_eq!(
        eval(&["assume(a > 0, a < 1)", "abs(ln(a))"]),
        expr("-ln(a)")
    );
    assert_eq!(eval(&["assume(a > b)", "abs(a - b)"]), expr("a - b"));
    assert_eq!(eval(&["assume(a > b, b > 0)", "sqrt(a^2)"]), "a");
    assert_eq!(
        eval(&["assume(a > b + 1)", "abs(b - a + exp(x))"]),
        expr("abs(b - a + exp(x))")
    );
    assert_eq!(
        eval(&["assume(a > b + 1)", "abs(a - b - 1 + exp(x))"]),
        expr("a - b - 1 + exp(x)")
    );
    assert_eq!(eval(&["assume(a > 2)", "piecewise(a > 1, x, y)"]), "x");
    assert_eq!(eval(&["assume(a > b)", "piecewise(b >= a, x, y)"]), "y");
}

#[test]
fn linear_limits() {
    assert_eq!(eval(&["assume(a > 1)", "lim(a^n, n, oo)"]), "+oo");
    assert_eq!(eval(&["assume(a > 0, a < 1)", "lim(a^n, n, oo)"]), "0");
}

#[test]
fn linear_solving() {
    assert_eq!(eval(&["assume(x > 1)", "solve(x^2 = 4)"]), "x = 2");
    assert_eq!(eval(&["assume(x > 3)", "solve(x^2 = 4)"]), "no solution");
    assert_eq!(
        eval(&["assume(x > y)", "solve(x^2 = 1, y^2 = 1)"]),
        "x = 1, y = -1"
    );
    assert_eq!(eval(&["assume(a > 1)", "solve(a^2 < 4)"]), "a ∈ (1, 2)");
    assert_eq!(
        eval(&["assume(x > y)", "solve(x^2 + y^2 < 1, x, y)"]),
        eval(&["solve(x^2 + y^2 < 1, x > y, x, y)"])
    );
}

#[test]
fn functions_of_inverse_functions_in_their_domain() {
    assert_eq!(eval(&["assume(x >= -1, x <= 1)", "cos(acos(x))"]), "x");
    assert_eq!(
        eval(&["assume(x >= -1, x <= 1)", "sin(acos(x))"]),
        expr("sqrt(1 - x^2)")
    );
    // `{$x = 1$}` is a pole of `{$tan(asin x)$}`
    assert_eq!(
        eval(&["assume(x >= -1, x <= 1)", "tan(asin(x))"]),
        "tan(asin(x))"
    );
    assert_eq!(eval(&["assume(x > -1, x < 1)", "tanh(atanh(x))"]), "x");
    assert_eq!(eval(&["assume(y > 1)", "cosh(acosh(y))"]), "y");
}
