//! Expressions over the complex numbers.
use formalith::{field::complex::C, parse, term::Expand};

mod common;
use common::{line, pretty};

fn eval(input: &str) -> String {
    line(&parse!(input, C))
}

#[test]
fn values_are_printed() {
    assert_eq!(eval("i"), "i");
    assert_eq!(eval("-i"), "-i");
    assert_eq!(eval("2*i"), "2*i");
    assert_eq!(eval("1+2*i"), "1+2*i");
    assert_eq!(eval("1/2-i"), "1/2-i");
    assert_eq!(eval("3"), "3");
}

#[test]
fn printed_values_are_parsed_back() {
    for input in ["i", "-i", "1+2*i", "1/2-3/4*i", "(1+i)*x", "x^(2*i)"] {
        let printed = eval(input);
        assert_eq!(eval(&printed), printed, "{input}");
    }
}

#[test]
fn compound_values_are_grouped() {
    assert_eq!(eval("(1+i)*x"), "(1+i)*x");
    assert_eq!(eval("x^(1+i)"), "x^(1+i)");
    assert_eq!(eval("(2*i)^(1/3)"), "(2*i)^(1/3)");
    assert_eq!(pretty(&parse!("(1+i)*x", C)), "(1 + i)⋅x");
}

#[test]
fn arithmetic() {
    assert_eq!(parse!("i^2", C), (-1).into());
    assert_eq!(parse!("i*i", C), (-1).into());
    assert_eq!(parse!("(1+i)*(1-i)", C), 2.into());
    assert_eq!(eval("1/(1+i)"), "1/2-1/2*i");
    assert_eq!(eval("i^-1"), "-i");
    assert_eq!(parse!("(1+i)^4", C), (-4).into());
    assert_eq!(eval("(2+3*i)-(2+i)"), "2*i");
    assert_eq!(eval("i*x+i*x"), "2*i*x");
}

#[test]
fn roots() {
    assert_eq!(eval("(-4)^(1/2)"), "2*i");
    assert_eq!(eval("(-4)^(3/2)"), "-8*i");
    assert_eq!(eval("(-4)^(-1/2)"), "-1/2*i");
    assert_eq!(parse!("4^(1/2)", C), 2.into());
    assert_eq!(eval("2^(1/2)"), "2^(1/2)");
}

#[test]
fn builtins() {
    assert_eq!(parse!("abs(3+4*i)", C), 5.into());
    assert_eq!(eval("abs(1+i)"), "2^(1/2)");
    assert_eq!(eval("re(3+4*i)"), "3");
    assert_eq!(eval("im(3+4*i)"), "4");
    assert_eq!(eval("conj(3+4*i)"), "3-4*i");
    assert_eq!(parse!("re(x+2+i)", C), parse!("re(x)+2", C));
    assert_eq!(parse!("re(i*x)", C), parse!("-im(x)", C));
    assert_eq!(
        parse!("conj((1+i)*x*y)", C),
        parse!("(1-i)*conj(x)*conj(y)", C)
    );
    assert_eq!(parse!("det([[i, 1], [1, i]])", C), (-2).into());
}

#[test]
fn expand_factor_simplify() {
    assert_eq!(parse!("(x+i)^2", C).expand(), parse!("x^2+2*i*x-1", C));
    assert_eq!(parse!("(i*x)^2", C).expand(), parse!("-x^2", C));
    assert_eq!(parse!("expand((x+i)*(x-i))", C), parse!("x^2+1", C));
    assert_eq!(parse!("(x^2-1)/(x-1)", C).simplify(), parse!("x+1", C));
    assert_eq!(parse!("(x+1)/((x+1)/x)", C).simplify(), parse!("x", C));
    assert_eq!(parse!("2*x/(4*x+2)", C).simplify(), parse!("x/(2*x+1)", C));
    assert_eq!(parse!("(2*i*y)^2", C), parse!("-4*y^2", C));
    assert_eq!(
        parse!("(x+i*y)^2 - (x-i*y)^2", C).expand(),
        parse!("4*i*x*y", C)
    );
    assert_eq!(parse!("factor(x^2-1)", C), parse!("(x+1)*(x-1)", C));
}

#[test]
fn factor_over_gaussian_rationals() {
    assert_eq!(parse!("factor(x^2+1)", C), parse!("(x-i)*(x+i)", C));
    assert_eq!(
        parse!("factor(x^4-1)", C),
        parse!("(x-i)*(x-1)*(x+1)*(x+i)", C)
    );
    assert_eq!(parse!("factor(x^2+y^2)", C), parse!("(x+i*y)*(x-i*y)", C));
    assert_eq!(parse!("factor(x^2-2*i*x-1)", C), parse!("(x-i)^2", C));
    assert_eq!(
        parse!("factor((1+i)*x^2+2*i*x)", C),
        parse!("(1+i)*x*(x+1+i)", C)
    );
    assert_eq!(parse!("factor(2*x^2+2)", C), parse!("2*(x-i)*(x+i)", C));
    assert_eq!(parse!("factor(x^2+x+1)", C), parse!("x^2+x+1", C));
}

#[test]
fn powers_of_i() {
    assert_eq!(eval("i^3"), "-i");
    assert_eq!(eval("i^4"), "1");
    assert_eq!(eval("i^100"), "1");
    assert_eq!(eval("i^101"), "i");
    assert_eq!(eval("1/i"), "-i");
    assert_eq!(eval("i*i*x"), "-x");
    assert_eq!(eval("0*i"), "0");
    assert_eq!(parse!("(1+i)^8", C), 16.into());
    assert_eq!(eval("(1+i)/(1-i)"), "i");
    assert_eq!(parse!("(2+3*i)*(2-3*i)", C), 13.into());
}

#[test]
fn square_roots_of_negative_values() {
    assert_eq!(eval("sqrt(-1)"), "i");
    assert_eq!(eval("sqrt(-4)"), "2*i");
    assert_eq!(eval("sqrt(i)"), "i^(1/2)");
}

#[test]
fn complex_polynomials() {
    assert_eq!(parse!("expand((x+i)*(x-i))", C), parse!("x^2+1", C));
    assert_eq!(parse!("factor(x^2+1)", C), parse!("(x-i)*(x+i)", C));
}

#[test]
fn complex_factors_are_printed_with_their_sign() {
    assert_eq!(eval("factor(x^2+1)"), "(x-i)*(x+i)");
}

#[test]
fn euler_identity_and_involutions() {
    assert_eq!(parse!("exp(i*pi)", C), (-1).into());
    assert_eq!(parse!("conj(conj(x))", C), parse!("x", C));
}
