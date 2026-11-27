//! Set selection and evaluation of the command line interface.
use formalith::{
    dynamic::{Coefficients, SetChoice},
    parser::environment::Environment,
};

fn parse(name: &str) -> Result<SetChoice, String> {
    name.parse()
}

#[test]
fn set_names() {
    for name in [
        "N", "Z", "R", "C", "M(R)", "M(C)", "M(Z)", "M(Z/6)", "Z/7", "R[x]", "C[t]", "Z/2[x]",
        "Z/7[y_1]",
    ] {
        assert_eq!(parse(name).map(SetChoice::name), Ok(name.to_owned()));
    }
    assert_eq!(parse("r"), Ok(SetChoice::R));
    assert_eq!(parse("z/7z"), Ok(SetChoice::Zn(7)));
    assert_eq!(parse(" Z / 7 "), Ok(SetChoice::Zn(7)));
    assert_eq!(parse("m(r)"), Ok(SetChoice::MR));
    assert_eq!(parse("M"), Ok(SetChoice::MR));
    assert_eq!(parse("m(c)"), Ok(SetChoice::MC));
    assert_eq!(parse("M( z/6z )"), Ok(SetChoice::MZn(6)));
    assert!(matches!(
        parse("Z/5[x]"),
        Ok(SetChoice::Poly(Coefficients::Zn(5), _))
    ));
}

#[test]
fn invalid_set_names() {
    for name in [
        "Q", "Z/1", "Z/0", "Z/x", "Z/-3", "Q[x]", "Z[x]", "M[x]", "R[2x]", "R[]", "C[i]", "R[abs]",
        "R[x", "M(Q)", "M(Z/1)", "M(Z", "M(M)",
    ] {
        assert!(parse(name).is_err(), "{name}");
    }
}

#[test]
fn eval() {
    let eval = |input, set: &str| {
        parse(set)
            .unwrap()
            .eval(input, false, &mut Environment::new())
    };
    assert_eq!(eval("3*5", "Z/7"), Ok("1".to_owned()));
    assert_eq!(
        eval("factor(x^4-1)", "Z/5"),
        eval("(x+1)*(x+2)*(x+3)*(x+4)", "Z/5")
    );
    assert_eq!(eval("gcd(x^2-1, x-1)", "R[x]"), eval("x-1", "R[x]"));
    assert_eq!(eval("(t+1)^2", "Z/2[t]"), eval("t^2+1", "Z/2[t]"));
    assert_eq!(
        eval("smith([[2,4],[6,8]])", "M(Z)"),
        eval("[[2,0],[0,4]]", "M(Z)")
    );
    assert_eq!(
        eval("smith([[2,4],[6,8]])", "M(Z/6)"),
        eval("[[2,0],[0,2]]", "M(Z/6)")
    );
    // Invertible over Z only with a determinant ±1
    for input in [
        "[[2,0],[0,2]]^-1",
        "1/[[2,0],[0,2]]",
        "[[1,1],[0,1]]/[[2,0],[0,2]]",
        "[[2,1,0],[1,1,0],[0,0,2]]^-1",
    ] {
        assert_eq!(eval(input, "M(Z)"), Ok("undefined".to_owned()), "{input}");
    }
    assert_eq!(
        eval("[[1,1],[0,1]]^-1", "M(Z)"),
        eval("[[1,-1],[0,1]]", "M(Z)")
    );
    assert_eq!(
        eval("[[2,0],[0,2]]^-1", "M"),
        eval("[[1/2,0],[0,1/2]]", "M")
    );
    assert_eq!(eval("x+1", "Z/2[x]"), Ok("x + 1".to_owned()));
    assert_eq!(eval("quo(17, 5)", "Z"), Ok("3".to_owned()));
    assert_eq!(eval("rem(-17, 5)", "Z"), Ok("3".to_owned()));
    assert_eq!(eval("quo(-17, 5)", "Z"), Ok("-4".to_owned()));
}

#[test]
fn eval_inequalities() {
    let eval = |input| SetChoice::R.eval(input, false, &mut Environment::new());
    assert_eq!(eval("x^2 <= 4"), Ok("x ∈ [-2, 2]".to_owned()));
    assert_eq!(eval("x^2 >= 0"), Ok("x ∈ ℝ".to_owned()));
    assert_eq!(eval("x^2*(x-1) >= 0"), Ok("x ∈ {0} ∪ [1, +∞)".to_owned()));
}

/// Matrix literals outside of matrices name the matrix set of the current set.
#[test]
fn matrix_hints() {
    for (set, matrices) in [
        (SetChoice::R, "M(R)"),
        (SetChoice::C, "M(C)"),
        (SetChoice::Z, "M(Z)"),
        (SetChoice::N, "M(Z)"),
        (SetChoice::Zn(7), "M(Z/7)"),
    ] {
        let err = set
            .try_evaluate("[[1, 2], [3, 4]]", &mut Environment::default())
            .unwrap_err();
        assert_eq!(
            err.hint(),
            Some(format!("matrices are in `{matrices}`: `:set {matrices}`").as_str()),
            "{set}"
        );
    }
    // A hint of the parser wins
    let err = SetChoice::N
        .try_evaluate("1 - 2", &mut Environment::default())
        .unwrap_err();
    assert!(err.hint().unwrap().contains("`Z`"));
    // Matrices are already right inside `det`, the error is elsewhere
    assert_eq!(SetChoice::R.hint("det([[1, 2], [3, 4]]) +"), None);
    assert!(SetChoice::R.hint("det([[1]]) + [[1]]").is_some());
    assert_eq!(SetChoice::MR.hint("[[1]] +"), None);
}
