//! Expressions over the natural integers `N`.
use std::cmp::Ordering;

use formalith::{
    field::{PartiallyOrderedSet, natural::N},
    parse, try_parse,
};
use malachite::Natural;

mod common;
use common::line;

#[test]
fn constants() {
    assert_eq!(line(&parse!("5", N)), "5");
    assert_eq!(
        line(&parse!("100000000000000000000", N)),
        "100000000000000000000"
    );
}

#[test]
fn symbols() {
    assert_eq!(line(&parse!("x", N)), "x");
}

#[test]
fn errors() {
    assert!(try_parse!("", N).is_err());
    assert!(try_parse!("5.5", N).is_err());
    assert!(try_parse!("-5", N).is_err());
    // No additive inverses, hence no subtraction, negation, division nor negative exponents
    for input in ["2 - 3", "x - x", "-x", "6/4", "x/x", "x^(0 - 1)", "x^(1/2)"] {
        assert!(try_parse!(input, N).is_err(), "{input}");
    }
}

#[test]
fn arithmetic() {
    for (input, expected) in [
        ("2+3", "5"),
        ("2*3", "6"),
        ("2^10", "1024"),
        ("2x + 3x", "5*x"),
        ("x + x", "2*x"),
        ("x*x", "x^2"),
        ("x*x^2", "x^3"),
        ("2*(3*x)", "6*x"),
        ("0*x + 1", "1"),
        ("x^0", "1"),
        ("+x", "x"),
    ] {
        assert_eq!(line(&parse!(input, N)), expected, "{input}");
    }
}

#[test]
fn builtins() {
    for (input, expected) in [
        ("gcd(4, 6)", "2"),
        ("lcm(4, 6)", "12"),
        ("factorial(5)", "120"),
        ("3!", "6"),
        ("quo(7, 3)", "2"),
        ("rem(7, 3)", "1"),
        ("isprime(7)", "1"),
        ("abs(4)", "4"),
    ] {
        assert_eq!(line(&parse!(input, N)), expected, "{input}");
    }
}

#[test]
fn unevaluated() {
    // Functions without values in `N` stay unevaluated instead of panicking
    for input in [
        "sin(x)",
        "integrate(x, x)",
        "x!",
        "I(2)",
        "det([[1, 2], [3, 4]])",
        "subs(x, x, 2)",
        "piecewise(x > 1, 2, 3)",
        "expand((x + 1)^2)",
    ] {
        assert!(try_parse!(input, N).is_ok(), "{input}");
    }
}

#[test]
fn ordering() {
    assert_eq!(
        N.partial_cmp(&Natural::from(2u32), &Natural::from(3u32)),
        Some(Ordering::Less)
    );
}
