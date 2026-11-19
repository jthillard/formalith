//! Assumptions on symbols with `assume`, like `a > 0` or `n integer`.
use formalith::{field::real::R, parse, parser::environment::Environment, repl::SetChoice};

mod common;
use common::{eval_statements, line};

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
    assert_eq!(eval(&["solve(a > 0)"]), "a ∈ (0, ∞)");
    assert_eq!(eval(&["assume(a < 0)", "solve(a^2 < 4)"]), "a ∈ (-2, 0)");
}

#[test]
fn assume_errors() {
    let err = |statements: &[&str]| eval_statements(SetChoice::R, statements, false).unwrap_err();
    assert!(err(&["assume(a > 0, a < 0)"]).contains("contradicts"));
    assert!(err(&["assume(a > 0)", "assume(a <= 0)"]).contains("contradicts"));
    assert!(err(&["assume(a > 1)"]).contains("compare a symbol with 0"));
    assert!(err(&["assume(a + 1 > 0)"]).contains("not a symbol"));
    assert!(err(&["assume(pi > 0)"]).contains("constant"));
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
    assert_eq!(eval(&["assume(a > 0)", "lim(exp(a*x), x, oo)"]), "oo");
    assert_eq!(eval(&["assume(a < 0)", "lim(exp(a*x), x, oo)"]), "0");
    assert_eq!(eval(&["assume(a > 0)", "lim(a*x, x, oo)"]), "oo");
    assert_eq!(eval(&["assume(a < 0)", "lim(a*x, x, oo)"]), "-oo");
    assert_eq!(eval(&["lim(a*x, x, oo)"]), expr("sign(a)*oo"));
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
    assert_eq!(formalith::repl::definitions(&env), "b := 2\nassume(a > 0)");
    formalith::repl::clear_definitions(&mut env, "a").unwrap();
    assert_eq!(formalith::repl::definitions(&env), "b := 2");
    assert!(formalith::repl::clear_definitions(&mut env, "a").is_err());
}

#[test]
fn typst_output() {
    assert_eq!(
        eval_statements(SetChoice::R, &["assume(a >= 0, n integer)"], true).unwrap(),
        "a >= 0, n in ZZ"
    );
}
