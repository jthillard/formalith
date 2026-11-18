//! Builtin functions evaluated during normalization.

use formalith::{field::real::R, parse, try_parse};

#[test]
fn expand() {
    assert_eq!(parse!("expand((x+1)^2)", R), parse!("x^2+2*x+1", R));
}

#[test]
fn factor() {
    assert_eq!(parse!("factor(x^2-1)", R), parse!("(x-1)*(x+1)", R));
    assert_eq!(parse!("factor(expand((x+1)^2))", R), parse!("(x+1)^2", R));
}

#[test]
fn simplify() {
    assert_eq!(parse!("simplify((x^2-1)/(x-1))", R), parse!("x+1", R));
}

#[test]
fn wrong_arity() {
    assert!(try_parse!("expand(x, y)", R).is_err());
    assert!(try_parse!("factor()", R).is_err());
}
