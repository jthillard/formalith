//! User definitions of variables and functions.
use formalith::{
    field::{complex::C, real::R},
    parse,
    parser::environment::{Environment, Statement},
    repl::SetChoice,
    try_parse,
};

/// Evaluate each statement in `R`, returning the result of the last one.
fn eval(statements: &[&str]) -> Result<String, String> {
    let mut env = Environment::new();
    let mut result = Ok(String::new());
    for statement in statements {
        result = SetChoice::R.eval(statement, false, &mut env);
    }
    result
}

fn ok(expression: &str) -> Result<String, String> {
    eval(&[expression])
}

#[test]
fn variables() {
    assert_eq!(eval(&["a := 2", "a^3"]), Ok("8".to_owned()));
    assert_eq!(eval(&["a := 1+1", "2*a"]), Ok("4".to_owned()));
    assert_eq!(eval(&["a := 1+1", "2^a"]), Ok("4".to_owned()));
    assert_eq!(eval(&["a := x + 1", "a^2 - a"]), ok("(x+1)^2 - (x+1)"));
    assert_eq!(eval(&["a := 2"]), Ok("a := 2".to_owned()));
}

#[test]
fn functions() {
    assert_eq!(eval(&["f(x) := x^2 + 1", "f(3)"]), Ok("10".to_owned()));
    assert_eq!(eval(&["f(x) := x^2 + 1", "f(y+1)"]), ok("(y+1)^2 + 1"));
    assert_eq!(eval(&["f(x, y) := x - y", "f(5, 2)"]), Ok("3".to_owned()));
    assert_eq!(
        eval(&["f(x, y) := x - y", "f(f(5, 2), (1))"]),
        Ok("2".to_owned())
    );
    assert_eq!(
        eval(&["f(x) := x^2", "g(x) := f(x)*2", "g(3)"]),
        Ok("18".to_owned())
    );
    assert_eq!(eval(&["f(x) := x^2", "f(x)"]), ok("x^2"));
    assert_eq!(eval(&["f(x) := abs(x)", "f(-2)"]), Ok("2".to_owned()));
}

#[test]
fn parameters_shadow_definitions() {
    assert_eq!(
        eval(&["x := 5", "f(x) := x + 1", "f(1)"]),
        Ok("2".to_owned())
    );
    assert_eq!(
        eval(&["x := 5", "f(x) := x + 1"]),
        Ok("f(x) := x + 1".to_owned())
    );
    // Arguments are parsed with the definitions of the caller
    assert_eq!(
        eval(&["y := 5", "f(x, y) := x * y", "f(y, 2)"]),
        Ok("10".to_owned())
    );
}

#[test]
fn snapshots() {
    assert_eq!(
        eval(&["a := 2", "b := a+1", "a := 5", "b"]),
        Ok("3".to_owned())
    );
    assert_eq!(eval(&["a := 5", "a := a + 1", "a"]), Ok("6".to_owned()));
    assert_eq!(eval(&["f(x) := f(x)", "f(2)"]), Ok("f(2)".to_owned()));
}

#[test]
fn errors() {
    assert!(eval(&["f(x) := x", "f(1, 2)"]).is_err());
    assert!(eval(&["f(x) := x", "f()"]).is_err());
    assert!(eval(&["f(x) := x", "f"]).is_err());
    assert!(eval(&["a := 1", "a(2)"]).is_err());
    assert!(ok("abs := 1").is_err());
    assert!(ok("f(abs) := 1").is_err());
    assert!(ok("f(x, x) := 1").is_err());
    assert!(ok("a := ").is_err());
    assert!(ok("a := 1 :=").is_err());
    assert!(ok("1 := 2").is_err());
    let mut env = Environment::new();
    assert!(SetChoice::C.eval("i := 1", false, &mut env).is_err());
    let poly = "R[x]".parse::<SetChoice>().unwrap();
    assert!(poly.eval("x := 1", false, &mut env).is_err());
    assert!(env.definitions().next().is_none());
}

#[test]
fn across_sets() {
    let mut env = Environment::new();
    SetChoice::R.eval("f(z) := z^2", false, &mut env).unwrap();
    assert_eq!(
        SetChoice::C.eval("f(i)", false, &mut env),
        Ok("-1".to_owned())
    );
    assert_eq!(
        "Z/7"
            .parse::<SetChoice>()
            .unwrap()
            .eval("f(3)", false, &mut env),
        Ok("2".to_owned())
    );
}

#[test]
fn library() {
    let mut env = Environment::new();
    let statement = env.eval("f(x, y) := x*y", R).unwrap();
    assert!(matches!(statement, Statement::Definition { ref params, .. } if params.len() == 2));
    assert_eq!(parse!("f(2, 3)", R, &env), parse!("6", R));
    assert_eq!(try_parse!("f(i, i)", C, &env), try_parse!("-1", C));
    assert_eq!(
        env.definitions()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        ["f(x, y) := x*y"]
    );
    assert!(env.remove("f"));
    assert!(!env.remove("f"));
    assert_eq!(parse!("f(2, 3)", R, &env).to_string(), "f(2, 3)");
}
