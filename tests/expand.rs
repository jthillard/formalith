//! Expansion, simplification, unification and factorization of expressions.
use formalith::{
    field::real::R,
    parse,
    term::{Expand, Unify},
};

#[test]
fn expand_products() {
    assert_eq!(parse!("2*(x+1)", R).expand(), parse!("2*x+2", R));
    assert_eq!(parse!("x*(x+1)", R).expand(), parse!("x^2+x", R));
    assert_eq!(parse!("-(x+1)", R).expand(), parse!("-x-1", R));
    assert_eq!(parse!("(x+2)*(x+3)", R).expand(), parse!("x^2+5*x+6", R));
    assert_eq!(
        parse!("(a+b)*(c+d)", R).expand(),
        parse!("a*c+a*d+b*c+b*d", R)
    );
    assert_eq!(parse!("(2*x)^2", R).expand(), parse!("4*x^2", R));
    assert_eq!(parse!("(x*y)^2", R).expand(), parse!("x^2*y^2", R));
}

#[test]
fn expand_powers() {
    assert_eq!(parse!("(x+1)^2", R).expand(), parse!("x^2+2*x+1", R));
    assert_eq!(parse!("(x-1)^2", R).expand(), parse!("x^2-2*x+1", R));
    assert_eq!(parse!("(x+1)^3", R).expand(), parse!("x^3+3*x^2+3*x+1", R));
    assert_eq!(
        parse!("(x+y)^3", R).expand(),
        parse!("x^3+3*x^2*y+3*x*y^2+y^3", R)
    );
    assert_eq!(
        parse!("(x+y+z)^2", R).expand(),
        parse!("x^2+y^2+z^2+2*x*y+2*x*z+2*y*z", R)
    );
    assert_eq!(
        parse!("(x+1)^5", R).expand(),
        parse!("x^5+5*x^4+10*x^3+10*x^2+5*x+1", R)
    );
    assert_eq!(parse!("(x+1)^1", R).expand(), parse!("x+1", R));
    assert_eq!(parse!("(x+1)^0", R).expand(), 1.into());
}

#[test]
fn expand_keeps_non_expandable() {
    for input in ["x", "x+y", "(x+1)^n", "(x+1)^-1", "2^(1/2)", "x^y", "5"] {
        let term = parse!(input, R);
        assert_eq!(term.expand(), term, "{input}");
    }
}

#[test]
fn expand_is_idempotent() {
    for input in ["(x+1)^3", "(a+b)*(c+d)", "(x+y+z)^2*x"] {
        let expanded = parse!(input, R).expand();
        assert_eq!(expanded.expand(), expanded, "{input}");
    }
}

#[test]
fn simplify_rational_expressions() {
    assert_eq!(parse!("x/(x+1) + 1/(x+1)", R).simplify(), 1.into());
    assert_eq!(parse!("x - (x+1)", R).simplify(), (-1).into());
    assert_eq!(parse!("(x+1)*(x-1)", R).simplify(), parse!("x^2-1", R));
    assert_eq!(
        parse!("1/(x+1) + 1/(x-1)", R).simplify(),
        parse!("2*x/(x^2-1)", R)
    );
    assert_eq!(parse!("1/x + 1/y", R).simplify(), parse!("(x+y)/(x*y)", R));
    assert_eq!(parse!("(x^2*y-y)/(x*y+y)", R).simplify(), parse!("x-1", R));
    assert_eq!(parse!("(x^2-y^2)/(x+y)", R).simplify(), parse!("x-y", R));
    assert_eq!(parse!("x/2+x/3", R).simplify(), parse!("5/6*x", R));
}

#[test]
fn simplify_nested_fractions() {
    assert_eq!(parse!("(x+1)/((x+1)/x)", R).simplify(), parse!("x", R));
    assert_eq!(
        parse!("((x+1)/(x-1))/((x+1)/x)", R).simplify(),
        parse!("x/(x-1)", R)
    );
    assert_eq!(parse!("1/(1/x+1/y)", R).simplify(), parse!("x*y/(x+y)", R));
}

#[test]
fn simplify_numeric_content() {
    assert_eq!(parse!("2*x/(4*x+2)", R).simplify(), parse!("x/(2*x+1)", R));
    assert_eq!(parse!("-2/(-4*x-2)", R).simplify(), parse!("1/(2*x+1)", R));
    assert_eq!(
        parse!("(6*x^2-6)/(4*x-4)", R).simplify(),
        parse!("3/2*x+3/2", R)
    );
}

#[test]
fn expand_cancels_terms() {
    assert_eq!(parse!("(-y)^2", R), parse!("y^2", R));
    assert_eq!(parse!("(2*y)^2", R), parse!("4*y^2", R));
    assert_eq!(parse!("(x+y)^2 - (x-y)^2", R).expand(), parse!("4*x*y", R));
    assert_eq!(parse!("x^2+x^3+2*x^2", R), parse!("3*x^2+x^3", R));
}

#[test]
fn as_fraction() {
    let (num, den) = parse!("2/3", R).as_fraction(false);
    assert_eq!((num, den), (2.into(), 3.into()));

    let (num, den) = parse!("x", R).as_fraction(false);
    assert_eq!((num, den), (parse!("x", R), 1.into()));

    let (num, den) = parse!("x^-2", R).as_fraction(false);
    assert_eq!((num, den), (1.into(), parse!("x^2", R)));

    let (num, den) = parse!("x/y + 1/2", R).as_fraction(false);
    assert_eq!((num, den), (parse!("2*x+y", R), parse!("2*y", R)));
}

#[test]
fn unify() {
    assert_eq!(parse!("x/y + 1/2", R).unify(), parse!("(2*x+y)/(2*y)", R));
    assert_eq!(parse!("x", R).unify(), parse!("x", R));
    assert_eq!(parse!("1/2", R).unify(), parse!("1/2", R));
}

#[test]
fn factor() {
    assert_eq!(parse!("x^2+2*x+1", R).factor(), parse!("(x+1)^2", R));
    assert_eq!(
        parse!("x^3-x^2-x+1", R).factor(),
        parse!("(x-1)^2*(x+1)", R)
    );
    assert_eq!(parse!("(x+1)^3", R).factor(), parse!("(x+1)^3", R));
    assert_eq!(parse!("x+1", R).factor(), parse!("x+1", R));
    assert_eq!(
        parse!("x^4-1", R).factor(),
        parse!("(x-1)*(x+1)*(x^2+1)", R)
    );
    assert_eq!(parse!("x^2-y^2", R).factor(), parse!("(x-y)*(x+y)", R));
    assert_eq!(parse!("2*x^2-2", R).factor(), parse!("2*(x-1)*(x+1)", R));
}

#[test]
fn expand_removes_zero_terms() {
    assert_eq!(parse!("(x+1)*(x-1)", R).expand(), parse!("x^2-1", R));
    assert_eq!(parse!("x - (x+1)", R).expand(), (-1).into());
}

#[test]
fn simplify_cancels_common_factors() {
    assert_eq!(parse!("(x^2-1)/(x-1)", R).simplify(), parse!("x+1", R));
    assert_eq!(parse!("(x^2-1)/(x+1)", R).simplify(), parse!("x-1", R));
}
