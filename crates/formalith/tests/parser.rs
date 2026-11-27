use formalith::{
    field::{
        Set,
        integer::Z,
        matrix::{M, VectorSpaceElement},
        modular::Zn,
        natural::N,
        real::R,
    },
    matrix::Matrix,
    parse, symbol, try_parse,
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
    let err = try_parse!("x^", R).unwrap_err();
    assert_eq!(
        err.to_string(),
        "expected an expression after `^`, found the end of the input"
    );
    assert_eq!(err.span(), Some(1..2));
}

/// Errors name the token they are about, and its bytes in the input.
#[test]
fn test_parse_error_spans() {
    let error = |input: &str| {
        let err = try_parse!(input, R).unwrap_err();
        (err.to_string(), err.span())
    };
    assert_eq!(error("2 $ 3"), ("unexpected `$`".to_owned(), Some(2..3)));
    assert_eq!(
        error("x +"),
        (
            "expected an expression after `+`, found the end of the input".to_owned(),
            Some(2..3)
        )
    );
    assert_eq!(
        error("f("),
        (
            "expected an argument, found the end of the input".to_owned(),
            Some(2..2)
        )
    );
    assert_eq!(
        error("(x + 1"),
        (
            "expected `)`, found the end of the input".to_owned(),
            Some(6..6)
        )
    );
    assert_eq!(error("sin(1, 2)").1, None);
    // After a character of two bytes
    assert_eq!(error("α + )").1, Some(0..2));
}

/// Matrix literals explain how matrices are written.
#[test]
fn test_parse_matrix_error_messages() {
    let err = try_parse!("[1, 2]", M).unwrap_err();
    assert_eq!(err.to_string(), "expected `[` starting a row, found `1`");
    assert_eq!(err.span(), Some(1..2));
    assert!(err.hint().unwrap().contains("[[1], [2]]"));
    assert_eq!(
        try_parse!("[[1, 2], [3]]", M).unwrap_err().to_string(),
        "the rows of a matrix must have the same length: row 2 has 1 entry, row 1 has 2 entries"
    );
}

/// Sets without negative numbers or fractions name the set which has them.
#[test]
fn test_parse_natural_hints() {
    for (input, set) in [
        ("1 - 2", "`Z`"),
        ("-3", "`Z`"),
        ("2/3", "`R`"),
        ("x^-1", "`R`"),
    ] {
        let err = try_parse!(input, N).unwrap_err();
        assert!(err.hint().unwrap().contains(set), "{input}: {err:?}");
    }
    assert_eq!(try_parse!("1 - 2", N).unwrap_err().span(), Some(2..3));
}

#[test]
fn test_parse_nested_det() {
    assert_eq!(parse!("det(det(det(5)))", R), 5.into());
}

#[test]
fn test_parse_trailing_input() {
    for input in [
        "5)", "5 5", "x 2", "(x+1)2", "5 $ 3", "x,y", "1..2", "abs 3",
    ] {
        assert!(try_parse!(input, R).is_err(), "{input:?}");
    }
}

#[test]
fn test_parse_scientific_notation() {
    for (input, expected) in [
        ("1e-20", "1/10^20"),
        ("1e3", "1000"),
        ("1.5E+3", "1500"),
        ("2.5e-1x", "x/4"),
        ("2e", "2*e"),
        ("2e-x", "2*e - x"),
    ] {
        assert_eq!(parse!(input, R), parse!(expected, R), "{input:?}");
    }
    assert_eq!(parse!("1e3", Z), parse!("1000", Z));
    assert!(try_parse!("1e-3", Z).is_err());
}

#[test]
fn test_parse_integer_exponents() {
    let z7 = Zn::new(7);
    for input in ["x^(1/2)", "x^(n/2)", "2^(1/3)"] {
        assert!(try_parse!(input, z7).is_err(), "{input:?}");
    }
    assert_eq!(parse!("x^(4/2)", z7), parse!("x^2", z7));
    assert!(try_parse!("x^-1", z7).is_ok());
    assert!(try_parse!("x^(1/2)", R.get_polynomial_ring(symbol!("x"))).is_err());
    // Exponents of `Z` are terms of `Z`, where `1/2` is allowed
    assert!(try_parse!("x^(1/2)", Z).is_ok());
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
        ("x y", "x*y"),
        ("5 x", "5*x"),
        ("2 (x + 1)", "2*(x + 1)"),
        ("(x+1)y", "(x+1)*y"),
        ("(x+1) y", "(x+1)*y"),
        ("(x+1) (x-1)", "(x+1)*(x-1)"),
        ("x y^2", "x*y^2"),
        ("a/b c", "a/b*c"),
        ("2 x y z", "2*x*y*z"),
        ("-x y + 1", "-x*y + 1"),
        ("sin(x) cos(x)", "sin(x)*cos(x)"),
        ("2 sin(x)", "2*sin(x)"),
        ("n! x", "factorial(n)*x"),
    ] {
        assert_eq!(parse!(input, R), parse!(expected, R), "{input:?}");
    }
    // A single identifier
    assert_ne!(parse!("xy", R), parse!("x*y", R));
    // An identifier followed by a parenthesis is a call, whatever the spacing
    assert_eq!(parse!("f (x)", R), parse!("f(x)", R));
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

#[test]
fn test_parse_more_errors() {
    for input in [
        "f(",
        "f()",
        "sin()",
        "log()",
        "3 4",
        "x == y",
        "x = y",
        "x :=",
        "sin x",
        "((x)",
        "x))",
        "(,)",
        "sin(,)",
        "1 +* 2",
        "lim(x, x)",
        "integrate(x)",
        "x^^2",
        "x**2",
    ] {
        assert!(try_parse!(input, R).is_err(), "{input:?}");
    }
}

#[test]
fn test_parse_builtin_arity_messages() {
    assert_eq!(
        try_parse!("sin(1, 2)", R).unwrap_err().to_string(),
        "`sin` expects 1 argument, found 2"
    );
    assert_eq!(
        try_parse!("log(1, 2, 3)", R).unwrap_err().to_string(),
        "`log` expects 1 to 2 arguments, found 3"
    );
    assert_eq!(
        try_parse!("lim(x, x)", R).unwrap_err().to_string(),
        "`lim` expects 3 to 4 arguments, found 2"
    );
}

#[test]
fn test_parse_unknown_characters_message() {
    let message = try_parse!("α + 1", R).unwrap_err().to_string();
    assert_ne!(message, "Input was empty");
}

#[test]
fn test_parse_nested_parentheses_and_signs() {
    assert_eq!(parse!("((((x))))", R), parse!("x", R));
    assert_eq!(parse!("-(-(-(x)))", R), parse!("-x", R));
    assert_eq!(parse!("- - x", R), parse!("x", R));
    assert_eq!(parse!("2*-3", R), (-6).into());
    assert_eq!(parse!("x^-2", R), parse!("1/x^2", R));
    assert_eq!(parse!("2^-1*4", R), 2.into());
    assert_eq!(parse!("-x^2", R), parse!("-(x^2)", R));
}

#[test]
fn test_parse_identifiers_with_digits_and_underscores() {
    assert_eq!(parse!("x1*x1", R), parse!("x1^2", R));
    assert_ne!(parse!("x_1 + x_2", R), parse!("2*x_1", R));
    assert_eq!(parse!("x_1 - x_1", R), 0.into());
}

#[test]
fn test_parse_decimal_literals() {
    assert_eq!(parse!("1.5x", R), parse!("3/2*x", R));
    assert_eq!(parse!("5.", R), 5.into());
    assert_eq!(parse!("0.125", R), parse!("1/8", R));
    assert_eq!(parse!("1.000", R), 1.into());
}

#[test]
fn test_parse_implicit_product_of_parentheses() {
    assert_eq!(parse!("(x+1)(x-1)", R), parse!("(x+1)*(x-1)", R));
}

#[test]
fn test_parse_long_input() {
    let sum = (1..=200)
        .map(|k| format!("{k}*x^{k}"))
        .collect::<Vec<_>>()
        .join("+");
    let term = parse!(&sum, R);
    assert_eq!(parse!(&format!("expand(({sum}) - ({sum}))"), R), 0.into());
    assert_ne!(term, 0.into());
    let nested = format!("{}x{}", "(".repeat(100), ")".repeat(100));
    assert_eq!(parse!(&nested, R), parse!("x", R));
}

#[test]
fn test_parse_factorial() {
    assert_eq!(parse!("3!", R), 6.into());
    assert_eq!(parse!("3!", Z), parse!("6", Z));
    assert_eq!(parse!("(n+1)!", R), parse!("factorial(n+1)", R));
    assert_eq!(parse!("n!^2", R), parse!("factorial(n)^2", R));
    assert_eq!(parse!("2^3!", R), 64.into());
    assert_eq!(parse!("-3!", R), (-6).into());
    assert_eq!(parse!("3!*x", R), parse!("6*x", R));
    assert_eq!(parse!("3!!", R), 720.into());
    assert_eq!(parse!("1/2!", R), parse!("1/2", R));
    assert!(try_parse!("!", R).is_err());
}
