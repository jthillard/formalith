//! Builtin functions evaluated during normalization.

use formalith::{
    context::Context,
    field::{complex::C, real::R},
    parse,
    term::Term,
    try_parse,
};

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
fn abs() {
    assert_eq!(parse!("abs(-3*x)", R), parse!("3*abs(x)", R));
    assert_eq!(parse!("abs(abs(x))", R), parse!("abs(x)", R));
    assert_eq!(parse!("abs(x)^2", R), parse!("x^2", R));
    assert_eq!(parse!("abs(x^2)", R), parse!("x^2", R));
    assert_eq!(parse!("abs(x^3)", R), parse!("abs(x)^3", R));
    assert_eq!(parse!("abs(x*y)^2", R), parse!("x^2*y^2", R));
    assert_eq!(parse!("sqrt(x^2)", R), parse!("abs(x)", R));
    assert_eq!(parse!("sqrt(x^4)", R), parse!("x^2", R));
    assert_eq!(parse!("(x^3)^(1/3)", R), parse!("x", R));
}

#[test]
fn floor_ceil_idempotent() {
    assert_eq!(parse!("floor(floor(x))", R), parse!("floor(x)", R));
    assert_eq!(parse!("ceil(floor(x))", R), parse!("floor(x)", R));
}

#[test]
fn radicals() {
    assert_eq!(parse!("sqrt(8)", R), parse!("2*2^(1/2)", R));
    assert_eq!(parse!("16^(1/3)", R), parse!("2*2^(1/3)", R));
    assert_eq!(parse!("sqrt(2)*sqrt(3)", R), parse!("6^(1/2)", R));
    assert_eq!(parse!("sqrt(18)/sqrt(2)", R), 3.into());
    assert_eq!(parse!("sqrt(8)+sqrt(2)", R), parse!("3*2^(1/2)", R));
}

#[test]
fn roots() {
    assert_eq!(parse!("sqrt(4)", R), 2.into());
    assert_eq!(parse!("sqrt(4/9)", R), parse!("2/3", R));
    assert_eq!(parse!("sqrt(x)", R), parse!("x^(1/2)", R));
    assert_eq!(parse!("root(27, 3)", R), 3.into());
    assert_eq!(parse!("root(x, n)", R), parse!("x^(1/n)", R));
    assert_eq!(parse!("sqrt(-4)", C), parse!("2*i", C));
    assert_eq!(parse!("root(x, 3)", C), parse!("x^(1/3)", C));
}

#[test]
fn sign() {
    assert_eq!(parse!("sign(-3)", R), (-1).into());
    assert_eq!(parse!("sign(0)", R), 0.into());
    assert_eq!(parse!("sign(1/2)", R), 1.into());
    assert_eq!(parse!("sign(x)", R).to_string(), "sign(x)");
}

#[test]
fn rounding() {
    assert_eq!(parse!("floor(7/2)", R), 3.into());
    assert_eq!(parse!("floor(-7/2)", R), (-4).into());
    assert_eq!(parse!("ceil(7/2)", R), 4.into());
    assert_eq!(parse!("ceil(-7/2)", R), (-3).into());
    assert_eq!(parse!("floor(3)", R), 3.into());
    assert_eq!(parse!("floor(x)", R).to_string(), "floor(x)");
}

#[test]
fn extremum() {
    assert_eq!(parse!("min(3, 1, 2)", R), 1.into());
    assert_eq!(parse!("max(3, 1, 2)", R), 3.into());
    assert_eq!(parse!("max(x)", R), parse!("x", R));
    assert_eq!(parse!("max(3, x, 1, x)", R), parse!("max(x, 3)", R));
    assert_eq!(parse!("min(x, y)", R).to_string(), "min(x, y)");
}

#[test]
fn gcd_lcm() {
    assert_eq!(parse!("gcd(12, 18)", R), 6.into());
    assert_eq!(parse!("lcm(4, 6)", R), 12.into());
    assert_eq!(parse!("gcd(0, 5)", R), 5.into());
    assert_eq!(parse!("gcd(1/2, 3/4)", R), parse!("1/4", R));
    assert_eq!(parse!("lcm(1/2, 3/4)", R), parse!("3/2", R));
    assert_eq!(parse!("gcd(x^2-1, x^2+2*x+1)", R), parse!("x+1", R));
    assert_eq!(parse!("lcm(x^2-1, x+1)", R), parse!("x^2-1", R));
    assert_eq!(parse!("gcd(x, 0)", R), parse!("x", R));
    assert_eq!(parse!("lcm(x, 0)", R), 0.into());
}

#[test]
fn wrong_arity() {
    assert!(try_parse!("expand(x, y)", R).is_err());
    assert!(try_parse!("factor()", R).is_err());
    assert!(try_parse!("sqrt(x, y)", R).is_err());
    assert!(try_parse!("root(x)", R).is_err());
    assert!(try_parse!("gcd(x, y, z)", R).is_err());
    assert!(try_parse!("min(x, y, z)", R).is_ok());
}

#[test]
fn diff() {
    assert_eq!(parse!("diff(x^3, x)", R), parse!("3*x^2", R));
    assert_eq!(parse!("diff(y, x)", R), parse!("0", R));
    assert_eq!(parse!("diff(5, x)", R), parse!("0", R));
    assert_eq!(parse!("diff(x*y + x^2, x)", R), parse!("y + 2*x", R));
    assert_eq!(parse!("diff((x+1)^2, x)", R), parse!("2*(x+1)", R));
    assert_eq!(parse!("diff(3*x*y*x, x)", R), parse!("6*x*y", R));
    assert_eq!(parse!("diff(sqrt(x), x)", R), parse!("1/2*x^(-1/2)", R));
    assert_eq!(parse!("diff(1/x, x)", R), parse!("-x^(-2)", R));
    assert_eq!(parse!("diff(diff(x^3, x), x)", R), parse!("6*x", R));
    assert_eq!(parse!("diff(i*x^2, x)", C), parse!("2*i*x", C));
}

#[test]
fn diff_unevaluated() {
    let is_diff = |term| matches!(term, Term::Fun(fun) if fun.get_ident() == Context::DIFF);
    assert!(is_diff(parse!("diff(x^x, x)", R)));
    assert_eq!(
        parse!("diff(f(x) + x^2, x)", R),
        parse!("diff(f(x), x) + 2*x", R)
    );
    assert!(is_diff(parse!("diff(x, 2)", R)));
}
