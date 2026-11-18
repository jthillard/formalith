//! Expressions over the integers modulo `n`.
use formalith::{field::modular::Zn, parse, try_parse};

mod common;
use common::{line, typst};

fn eval(input: &str, n: u64) -> String {
    line(&parse!(input, Zn::new(n)))
}

#[test]
fn arithmetic() {
    assert_eq!(eval("3+5", 7), "1");
    assert_eq!(eval("3*5", 7), "1");
    assert_eq!(eval("2-5", 7), "4");
    assert_eq!(eval("-1", 7), "6");
    assert_eq!(eval("10", 7), "3");
    assert_eq!(eval("2^10", 7), "2");
    assert_eq!(eval("3^1000000000000", 7), "4");
    assert_eq!(eval("7*x", 7), "0");
}

#[test]
fn inverses() {
    assert_eq!(eval("2^-1", 7), "4");
    assert_eq!(eval("1/3", 7), "5");
    assert_eq!(eval("2/3*3", 7), "2");
    // 2 isn't invertible modulo 6
    assert_eq!(eval("2^-1", 6), "2^-1");
    assert_eq!(eval("5^-1", 6), "5");
}

#[test]
fn moduli_are_distinct_sets() {
    assert_ne!(parse!("3", Zn::new(5)), parse!("3", Zn::new(7)));
    assert_eq!(parse!("8", Zn::new(5)), parse!("3", Zn::new(5)));
}

#[test]
fn symbols() {
    assert_eq!(eval("x+x+x", 3), "0");
    assert_eq!(eval("expand((x+1)^2)", 2), eval("x^2+1", 2));
    assert_eq!(eval("expand((x+1)^3)", 3), eval("x^3+1", 3));
}

#[test]
fn factor() {
    assert_eq!(eval("factor(x^2+1)", 2), eval("(x+1)^2", 2));
    assert_eq!(eval("factor(x^2+1)", 5), eval("(x+2)*(x+3)", 5));
    assert_eq!(eval("factor(x^4+x+1)", 2), eval("x^4+x+1", 2));
    assert_eq!(
        eval("factor(x^5-x)", 5),
        eval("x*(x+1)*(x+2)*(x+3)*(x+4)", 5)
    );
    assert_eq!(eval("factor(2*x^2+2)", 3), eval("2*(x^2+1)", 3));
    assert_eq!(eval("factor(x^3+1)", 3), eval("(x+1)^3", 3));
    // Not a field, or not univariate: left as is
    assert_eq!(eval("factor(x^2+1)", 4), "factor(x^2+1)");
}

#[test]
fn printing() {
    assert_eq!(
        typst(&parse!("3*x^2+1", Zn::new(7))),
        typst(&parse!("3*x^2+1", Zn::new(11)))
    );
}

#[test]
fn errors() {
    assert!(try_parse!("1.5", Zn::new(7)).is_err());
}
