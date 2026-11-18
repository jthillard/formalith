//! Expressions over polynomial rings `K[x]`.
use formalith::{
    field::{Set, complex::C, modular::Zn, real::R},
    parse, symbol,
};

mod common;
use common::{line, typst};

fn eval(input: &str) -> String {
    line(&parse!(input, R.get_polynomial_ring(symbol!("x"))))
}

#[test]
fn polynomials_are_expanded() {
    assert_eq!(eval("(x+1)^2"), eval("x^2+2*x+1"));
    assert_eq!(eval("(x+1)*(x-1)"), eval("x^2-1"));
    assert_eq!(eval("x*x-x^2"), "0");
    assert_eq!(eval("(x^2+1)/2"), eval("1/2*x^2+1/2"));
}

#[test]
fn printing() {
    assert_eq!(eval("x^2+2*x+1"), "x^2+2*x+1");
    assert_eq!(eval("x^3-x"), "x^3-x");
    assert_eq!(eval("3"), "3");
    assert_eq!(eval("0"), "0");
    for input in ["x^2+2*x+1", "x^3-1/2*x", "-x", "2*x"] {
        let printed = eval(input);
        assert_eq!(eval(&printed), printed, "{input}");
    }
    assert_eq!(
        typst(&parse!("x^2/2+1", R.get_polynomial_ring(symbol!("x")))),
        typst(&parse!("x^2/2+1", R))
    );
}

#[test]
fn symbolic_coefficients() {
    assert_eq!(eval("a*x+a*x"), eval("2*x*a"));
    assert_eq!(eval("a*(x+1)-a*x"), "a");
}

#[test]
fn inverses() {
    assert_eq!(eval("2^-1"), "1/2");
    // `x` isn't invertible
    assert_eq!(eval("x^-1"), "x^-1");
}

#[test]
fn euclidean_division() {
    assert_eq!(eval("quo(x^3+1, x-1)"), eval("x^2+x+1"));
    assert_eq!(eval("rem(x^3+1, x-1)"), "2");
    assert_eq!(eval("rem(x^2-1, x+1)"), "0");
    assert_eq!(eval("quo(x, 0)"), "quo(x, 0)");
}

#[test]
fn gcd_lcm() {
    assert_eq!(eval("gcd(x^2-1, x^2+2*x+1)"), eval("x+1"));
    assert_eq!(eval("gcd(2*x+2, 0)"), eval("x+1"));
    assert_eq!(eval("gcd(x, x+1)"), "1");
    assert_eq!(eval("lcm(x^2-1, x+1)"), eval("x^2-1"));
    assert_eq!(eval("lcm(x, 0)"), "0");
}

#[test]
fn other_variables() {
    let r_t = R.get_polynomial_ring(symbol!("t"));
    assert_eq!(line(&parse!("(t+1)^2", r_t)), "t^2+2*t+1");
    // `x` is a symbol of R[t]
    assert_eq!(parse!("x*t+x*t", r_t), parse!("2*t*x", r_t));
}

#[test]
fn other_coefficients() {
    let c_x = C.get_polynomial_ring(symbol!("x"));
    assert_eq!(parse!("(x+i)*(x-i)", c_x), parse!("x^2+1", c_x));

    let z2_x = Zn::new(2).get_polynomial_ring(symbol!("x"));
    assert_eq!(parse!("(x+1)^2", z2_x), parse!("x^2+1", z2_x));
    assert_eq!(parse!("gcd(x^2+1, x^2+x)", z2_x), parse!("x+1", z2_x));
    assert_eq!(parse!("rem(x^3+x+1, x^2+1)", z2_x), parse!("1", z2_x));
}
