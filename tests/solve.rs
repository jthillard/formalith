//! Solving systems of equations.
use formalith::{parser::environment::Environment, repl::SetChoice};

/// Evaluate each statement in `set`, returning the result of the last one.
fn eval_in(set: &str, statements: &[&str], typst: bool) -> Result<String, String> {
    let set: SetChoice = set.parse().unwrap();
    let mut env = Environment::new();
    let mut result = Ok(String::new());
    for statement in statements {
        result = set.eval(statement, typst, &mut env);
    }
    result
}

/// Solve `system` in `set`, printed as Typst so that the output doesn't depend on colors.
fn solve_in(set: &str, system: &str) -> Result<String, String> {
    eval_in(set, &[system], true)
}

fn solve(system: &str) -> Result<String, String> {
    solve_in("R", system)
}

fn ok(solution: &str) -> Result<String, String> {
    Ok(solution.to_owned())
}

#[test]
fn unique_solution() {
    assert_eq!(solve("x + y = 3, x - y = 1"), ok("x = 2, y = 1"));
    assert_eq!(solve("x + 2*y = 5, 3*x - y = 1"), ok("x = 1, y = 2"));
    assert_eq!(solve("2*x = 3"), ok("x = frac(3, 2)"));
    // Unknowns appear on both sides
    assert_eq!(solve("2*x + 1 = x - 3"), ok("x = -4"));
    // Unknowns are sorted by name
    assert_eq!(solve("b = 1, a = b + 1"), ok("a = 2, b = 1"));
}

#[test]
fn parametric_solution() {
    // `y` is free
    assert_eq!(
        solve("x + y = 1, 2*x + 2*y = 2"),
        solve_in("R", "x = 1 - y")
    );
    assert_eq!(solve("x = x"), ok("\"true\""));
    assert_eq!(solve("0 = 0"), ok("\"true\""));
}

#[test]
fn no_solution() {
    assert_eq!(solve("x + y = 1, x + y = 2"), ok("\"no solution\""));
    assert_eq!(solve("1 = 2"), ok("\"no solution\""));
}

#[test]
fn other_sets() {
    assert_eq!(solve_in("C", "x + i*y = 1, x - y = i"), ok("x = 0, y = -i"));
    assert_eq!(solve_in("Z/7", "3*x = 1"), ok("x = 5"));
    assert_eq!(solve_in("Z/7", "x + y = 2, x - y = 3"), ok("x = 6, y = 3"));
    // Pivots are one
    assert_eq!(solve_in("Z", "x + y = 3, x + 2*y = 5"), ok("x = 1, y = 2"));
    assert_eq!(solve_in("Z", "x + y = 1, x + y = 3"), ok("\"no solution\""));
}

#[test]
fn errors() {
    assert!(solve("x*y = 1").unwrap_err().contains("not linear"));
    assert!(solve("x^2 = 1").unwrap_err().contains("not linear"));
    assert!(
        solve_in("Z/6", "2*x = 1")
            .unwrap_err()
            .contains("not invertible")
    );
    assert!(
        solve_in("Z", "2*x = 4")
            .unwrap_err()
            .contains("not invertible")
    );
    assert!(
        solve_in("N", "x = 1")
            .unwrap_err()
            .contains("can't be solved")
    );
    assert!(
        solve_in("M", "x = 1")
            .unwrap_err()
            .contains("can't be solved")
    );
    assert_eq!(
        solve("x = 1, 2"),
        Err("expected `=` in each equation of a system".to_owned())
    );
    assert_eq!(
        solve("x = "),
        Err("Expression expected at position 4".to_owned())
    );
    assert!(solve("x = 1 = 2").is_err());
}

#[test]
fn expressions() {
    // Without `=`, a statement is still an expression
    assert_eq!(solve("1 + 2"), ok("3"));
    assert_eq!(solve(""), Err("Input was empty".to_owned()));
}

#[test]
fn definitions() {
    assert_eq!(eval_in("R", &["a := 2", "x + a = 3"], true), ok("x = 1"));
    assert_eq!(
        eval_in("R", &["f(t) := 2*t", "f(x) = 4"], true),
        ok("x = 2")
    );
}
