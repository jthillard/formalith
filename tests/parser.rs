use formalith::{
    field::{
        Set,
        matrix::{M, VectorSpaceElement},
        real::R,
    },
    matrix::Matrix,
    parse, try_parse,
};
use malachite::Rational;

#[test]
fn test_parse() {
    assert_eq!(parse!("5", R), 5.into());
    assert_eq!(
        parse!("5.5^2", R),
        Rational::try_from_float_simplest(30.25).unwrap().into()
    );
    assert_eq!(
        parse!("[[5]]", M),
        VectorSpaceElement::Vector(Matrix::new((1, 1), vec![5.into()], R.get_term_set())).into()
    );
}
#[test]
fn test_try_parse() {
    assert!(try_parse!("5+", R).is_err());
    assert_eq!(try_parse!("-+-+--5", R), Ok(5.into()));
    assert!(try_parse!("[5]", R).is_err());
    // Function arguments in another set can be nested arbitrarily deep
    assert_eq!(
        try_parse!("det(det(det(det(det(det(det(det(det(det(5))))))))))", R),
        Ok(5.into())
    );
}

#[test]
fn test_parse_whitespace() {
    assert_eq!(parse!("  x  +  1  ", R), parse!("x+1", R));
    assert_eq!(parse!("\tx\n*\n2", R), parse!("2*x", R));
}

#[test]
fn test_parse_parentheses() {
    assert_eq!(parse!("(((x)))", R), parse!("x", R));
    assert_eq!(parse!("((1+2)*(3+4))", R), 21.into());
    assert_eq!(parse!("2*(3+(4*(5+6)))", R), 94.into());
}

#[test]
fn test_parse_precedence() {
    assert_eq!(parse!("1+2*3", R), 7.into());
    assert_eq!(parse!("1*2+3", R), 5.into());
    assert_eq!(parse!("2*3^2", R), 18.into());
    assert_eq!(parse!("-x^2", R), parse!("-(x^2)", R));
    assert_eq!(parse!("2/3*3", R), 2.into());
    assert_eq!(parse!("8-2-1", R), 5.into());
    assert_eq!(parse!("8/2/2", R), 2.into());
}

#[test]
fn test_parse_floats() {
    assert_eq!(parse!("0.5", R), Rational::from_signeds(1, 2).into());
    assert_eq!(parse!("5.", R), 5.into());
    assert_eq!(parse!("1.25", R), Rational::from_signeds(5, 4).into());
}

#[test]
fn test_parse_identifiers() {
    for input in ["x", "xy", "x1", "x_1", "_x", "alpha"] {
        assert!(try_parse!(input, R).is_ok(), "{input}");
    }
    // Unknown functions stay unevaluated
    assert!(try_parse!("foo(3)", R).is_ok());
}

#[test]
fn test_parse_errors() {
    for input in [
        "", " ", "(5", "5+", "x^", "3*", "3/", "^2", "*3", "@", "{x}", "[x]", ".5",
    ] {
        assert!(try_parse!(input, R).is_err(), "{input:?}");
    }
}

#[test]
fn test_parse_error_messages() {
    assert_eq!(
        try_parse!("", R).unwrap_err().to_string(),
        try_parse!(" ", R).unwrap_err().to_string()
    );
    assert!(
        try_parse!("x^", R)
            .unwrap_err()
            .to_string()
            .contains("position 2")
    );
}

#[test]
fn test_parse_nested_det() {
    assert_eq!(parse!("det(det(det(5)))", R), 5.into());
}

#[test]
fn test_parse_trailing_input() {
    for input in [
        "5 x", "5)", "5 5", "x y", "5 $ 3", "x,y", "1..2", "1e3", "abs 3", "2 (x)",
    ] {
        assert!(try_parse!(input, R).is_err(), "{input:?}");
    }
}

#[test]
fn test_parse_implicit_product() {
    for (input, expected) in [
        ("2x", "2*x"),
        ("2(x + 1)", "2*(x + 1)"),
        ("3sqrt(x)", "3*sqrt(x)"),
        ("2x^2", "2*x^2"),
        ("1/2x", "x/2"),
        ("-2x", "-2*x"),
        ("acos(2x/(1+x^2))", "acos(2*x/(1+x^2))"),
    ] {
        assert_eq!(parse!(input, R), parse!(expected, R), "{input:?}");
    }
}

#[test]
fn test_parse_empty_parentheses() {
    assert!(try_parse!("()", R).is_err());
    assert!(try_parse!("abs()", R).is_err());
}

#[test]
fn test_parse_function_arity() {
    assert!(try_parse!("abs(1,2)", R).is_err());
    assert!(try_parse!("det(5,6)", R).is_err());
}
