//! Expressions over the integers `Z`.
use formalith::{field::integer::Z, parse, try_parse};

use crate::common::line;

#[test]
fn constants() {
    assert_eq!(line(&parse!("5", Z)), "5");
    assert_eq!(line(&parse!("-5", Z)), "-5");
    assert_eq!(line(&parse!("5+3", Z)), "8");
    assert_eq!(line(&parse!("2*3", Z)), "6");
    assert_eq!(line(&parse!("2-7", Z)), "-5");
    assert_eq!(line(&parse!("--7", Z)), "7");
}

#[test]
fn symbols() {
    assert_eq!(parse!("x+x", Z), parse!("2*x", Z));
    assert_eq!(parse!("x^2*x", Z), parse!("x^3", Z));
    assert_eq!(parse!("2*3+x", Z), parse!("x+6", Z));
    assert_eq!(parse!("x-x", Z), parse!("0", Z));
}

#[test]
fn non_invertible_values_stay_symbolic() {
    assert_eq!(line(&parse!("1/2", Z)), "2^-1");
    assert_eq!(line(&parse!("x^-1", Z)), "x^-1");
}

#[test]
fn errors() {
    assert!(try_parse!("", Z).is_err());
    assert!(try_parse!("3*", Z).is_err());
    assert!(try_parse!("(3", Z).is_err());
}

#[test]
fn powers() {
    assert_eq!(line(&parse!("2^10", Z)), "1024");
    assert_eq!(line(&parse!("10^20", Z)), "100000000000000000000");
    assert_eq!(parse!("7/7", Z), parse!("1", Z));
}

#[test]
fn float_is_not_an_integer() {
    assert!(try_parse!("5.5", Z).is_err());
}

#[test]
fn abs() {
    assert_eq!(line(&parse!("abs(-3)", Z)), "3");
}

#[test]
fn exact_division_and_euclidean_operations() {
    assert_eq!(line(&parse!("6/3", Z)), "2");
    assert_eq!(line(&parse!("7/2", Z)), "7*(2^-1)");
    assert_eq!(line(&parse!("quo(7, 2)", Z)), "3");
    assert_eq!(line(&parse!("rem(-7, 2)", Z)), "1");
    assert_eq!(line(&parse!("(-3)^3", Z)), "-27");
    assert_eq!(line(&parse!("2^100", Z)), "1267650600228229401496703205376");
}

#[test]
fn integer_builtins() {
    assert_eq!(line(&parse!("gcd(12, 18)", Z)), "6");
    assert_eq!(line(&parse!("lcm(4, 6)", Z)), "12");
    assert_eq!(line(&parse!("factorial(5)", Z)), "120");
}

#[test]
fn factor() {
    assert_eq!(
        parse!("factor(2*x^2 + 3*x + 1)", Z),
        parse!("(2*x + 1)*(x + 1)", Z)
    );
    assert_eq!(
        parse!("factor(6*x^2 - 6)", Z),
        parse!("6*(x - 1)*(x + 1)", Z)
    );
    assert_eq!(
        parse!("factor(3*x^3 + 6*x^2)", Z),
        parse!("3*x^2*(x + 2)", Z)
    );
    assert_eq!(
        parse!("factor(4*x^2 + 12*x + 9)", Z),
        parse!("(2*x + 3)^2", Z)
    );
    assert_eq!(
        parse!("factor(4*x^2*y - y)", Z),
        parse!("y*(2*x - 1)*(2*x + 1)", Z)
    );
    assert_eq!(
        parse!("factor(2*x*y + 2*x + 3*y + 3)", Z),
        parse!("(2*x + 3)*(y + 1)", Z)
    );
}

#[test]
fn expand() {
    assert_eq!(line(&parse!("expand((x+1)^2)", Z)), "2*x+x^2+1");
    assert_eq!(line(&parse!("expand((2*x*y)^3)", Z)), "8*(x^3)*(y^3)");
}
