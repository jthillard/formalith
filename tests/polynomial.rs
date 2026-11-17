//! Multivariate polynomials built from terms.
use formalith::{
    context::Symbol,
    field::real::R,
    parse,
    polynom::{MultivariatePolynomial, ToTerm},
    symbol,
};
use malachite::Rational;

mod common;
use common::{line, pretty};

macro_rules! poly {
    ($input:expr) => {
        parse!($input, R).to_polynomial()
    };
}

#[test]
fn constants() {
    let c: MultivariatePolynomial<Symbol, _, _> =
        MultivariatePolynomial::constant(Rational::from(3), R, R);
    assert!(c.is_constant());
    assert!(!c.is_one());
    assert!(!c.is_zero());

    let one: MultivariatePolynomial<Symbol, _, _> = MultivariatePolynomial::one(R, R);
    assert!(one.is_constant());
    assert!(one.is_one());

    let zero: MultivariatePolynomial<Symbol, _, _> = MultivariatePolynomial::zero(R, R);
    assert!(zero.is_zero());
    assert!(!zero.is_one());
}

#[test]
fn variable() {
    let x = MultivariatePolynomial::variable(symbol!("x"), R, R);
    assert!(!x.is_constant());
    assert!(!x.is_zero());
    assert_eq!(line(&x), "x^1");
}

#[test]
fn round_trip_through_terms() {
    for input in ["x^2+2*x+1", "x*y+3", "5", "x", "x^3*y^2-x*y+2"] {
        assert_eq!(poly!(input).to_term(), parse!(input, R), "{input}");
    }
}

#[test]
fn to_polynomial_expands() {
    assert_eq!(poly!("(x+1)^2"), poly!("x^2+2*x+1"));
    assert_eq!(poly!("(x+1)*(x-1)"), poly!("x^2-1"));
}

#[test]
fn arithmetic() {
    let a = poly!("x+1");
    let b = poly!("x-1");
    assert_eq!(&a + &b, poly!("2*x"));
    assert_eq!(a.clone() + b.clone(), poly!("2*x"));
    assert_eq!(a.clone() + &b, poly!("2*x"));
    assert_eq!(&a - &b, poly!("2"));
    assert_eq!(&a * &b, poly!("x^2-1"));
    assert_eq!(a.clone() * b.clone(), poly!("x^2-1"));
    assert_eq!(a.clone() * &b, poly!("x^2-1"));
    assert!((&a - &a).is_zero());
}

#[test]
fn quotient_remainder() {
    let (q, r) = poly!("x^2-1").quot_rem(&poly!("x-1"));
    assert_eq!(q, poly!("x+1"));
    assert!(r.is_zero());

    let (q, r) = poly!("x^3+2*x+1").quot_rem(&poly!("x+1"));
    assert_eq!(q, poly!("x^2-x+3"));
    assert_eq!(r, poly!("-2"));

    let (q, r) = poly!("x^3-1").quot_rem(&poly!("x-1"));
    assert_eq!(q, poly!("x^2+x+1"));
    assert!(r.is_zero());

    let (q, r) = poly!("2*x^2").quot_rem(&poly!("2"));
    assert_eq!(q, poly!("x^2"));
    assert!(r.is_zero());
}

#[test]
fn quotient_remainder_identity() {
    for (a, b) in [
        ("x^4+3*x^2-x+7", "x^2+1"),
        ("x^5-1", "x^2-x+1"),
        ("3*x^3+x", "2*x+1"),
    ] {
        let (a, b) = (poly!(a), poly!(b));
        let (q, r) = a.quot_rem(&b);
        assert_eq!(&(&q * &b) + &r, a);
    }
}

#[test]
fn gcd() {
    assert_eq!(poly!("x^2-1").gcd(&poly!("x-1")), poly!("x-1"));
    assert_eq!(poly!("x^2+2*x+1").gcd(&poly!("x^2-1")), poly!("x+1"));
    assert!(poly!("x+1").gcd(&poly!("x+2")).is_one());
    assert_eq!(
        poly!("(x+1)^2*(x+2)").gcd(&poly!("(x+1)*(x+3)")),
        poly!("x+1")
    );
}

#[test]
fn gcd_with_symbolic_exponents() {
    assert_eq!(poly!("x^(2*n)").gcd(&poly!("x^n")), poly!("x^n"));
}

#[test]
fn derivative() {
    let x = parse!("x", R);
    assert_eq!(poly!("x^3+2*x+1").derivative(&x), poly!("3*x^2+2"));
    assert_eq!(
        poly!("x^2*y+y").derivative(&x).to_term(),
        parse!("2*x*y", R)
    );
    assert!(poly!("5").derivative(&x).is_zero());
}

#[test]
fn square_free_factorization() {
    let factors = poly!("(x+1)^2*(x+2)").square_free_factorization();
    assert_eq!(factors, vec![(poly!("x+2"), 1), (poly!("x+1"), 2)]);

    let factors = poly!("(x+1)^3").square_free_factorization();
    assert_eq!(factors, vec![(poly!("x+1"), 3)]);

    let factors = poly!("x^3-x^2-x+1").factor();
    assert_eq!(factors, vec![(poly!("x+1"), 1), (poly!("x-1"), 2)]);

    let factors = poly!("7").square_free_factorization();
    assert_eq!(factors, vec![(poly!("7"), 1)]);
}

#[test]
fn leading_term_and_separate_variable() {
    let p = poly!("x^2+2*x+1");
    let (vars, coeff) = p.leading_term();
    assert_eq!(coeff, 1.into());
    assert_eq!(vars, vec![(parse!("x", R), 2.into())]);

    let (coefficients, exponents) = poly!("x^2*y+3*x").separate_variable(&parse!("x", R));
    assert_eq!(coefficients.len(), 2);
    assert_eq!(exponents.len(), 2);
    assert!(exponents.contains(&2.into()));
    assert!(exponents.contains(&1.into()));
}

#[test]
fn printing() {
    assert_eq!(line(&poly!("x^3+2*x+1")), "x^3+2*x^1+1");
    assert_eq!(pretty(&poly!("x^3+2*x+1")), " 3          \nx  + 2⋅x + 1");
}

#[test]
fn printing_signs_and_zero() {
    assert_eq!(line(&poly!("x-1")), "x^1-1");
    let p = poly!("x");
    assert_eq!(line(&(&p - &p)), "0");
}

#[test]
fn multivariate_results_are_canonical() {
    let x = parse!("x", R);
    assert_eq!(poly!("x^2*y+y").derivative(&x), poly!("2*x*y"));
    for _ in 0..20 {
        // `x*y` and `-y*x` are sometimes not merged
        assert_eq!(
            (&poly!("x+y") * &poly!("x-y")).to_term(),
            parse!("x^2-y^2", R)
        );
        assert_eq!(&poly!("x+y") * &poly!("x-y"), poly!("x^2-y^2"));
    }
}
