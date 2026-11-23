//! Expressions over the integers modulo `n`.
use formalith::{
    dynamic::SetChoice, field::modular::Zn, parse, parser::environment::Environment, try_parse,
};

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

#[test]
fn characteristic_two() {
    assert_eq!(eval("1+1", 2), "0");
    assert_eq!(eval("x+x", 2), "0");
    assert_eq!(eval("expand((x+y)^2)", 2), eval("x^2+y^2", 2));
    assert_eq!(eval("expand((x+1)^4)", 2), eval("x^4+1", 2));
}

#[test]
fn fermat_little_theorem() {
    assert_eq!(
        eval("factor(x^7-x)", 7),
        eval("x*(x+1)*(x+2)*(x+3)*(x+4)*(x+5)*(x+6)", 7)
    );
    assert_eq!(eval("123456^(13-1)", 13), "1");
    assert_eq!(eval("3^1000000006", 1_000_000_007), "1");
}

#[test]
fn large_modulus() {
    let p = 1_000_000_007;
    assert_eq!(eval("2^-1*2", p), "1");
    assert_eq!(eval("1000000006*1000000006", p), "1");
    assert_eq!(eval("-1", p), "1000000006");
}

#[test]
fn zero_divisors() {
    assert_eq!(eval("2*3", 6), "0");
    assert_eq!(eval("1/5", 6), "5");
    assert_eq!(eval("0^0", 7), "1");
    assert_eq!(eval("1/0", 7), "0^-1");
}

#[test]
fn degree() {
    // The leading coefficient vanishes modulo 7
    assert_eq!(eval("degree(7*x^2 + x, x)", 7), "1");
    assert_eq!(eval("degree(x^6 + 1, x)", 7), "6");
    // 7 isn't a natural number modulo 7
    assert!(eval("degree(x^7 + 1, x)", 7).starts_with("degree"));
}

#[test]
fn irreducible_polynomials_modulo_p() {
    assert_eq!(eval("factor(x^2+1)", 7), eval("x^2+1", 7));
    // x^4+1 is reducible modulo every prime
    assert_ne!(eval("factor(x^4+1)", 3), eval("x^4+1", 3));
    assert_ne!(eval("factor(x^4+1)", 13), eval("x^4+1", 13));
}

#[test]
#[should_panic(expected = "The modulus must be between 2 and 2^63")]
fn modulus_one_is_rejected() {
    let _ = Zn::new(1);
}

#[test]
fn powers_of_powers() {
    let eval = |input: &str| SetChoice::Zn(7).eval(input, false, &mut Environment::new());
    assert_eq!(eval("(x^3)^4 - x^12"), Ok("0".to_owned()));
    assert_eq!(eval("(x^2)^2"), eval("x^4"));
    assert_eq!(
        SetChoice::Z.eval("((x + 1)^2)^3 - (x + 1)^6", false, &mut Environment::new()),
        Ok("0".to_owned())
    );
}

#[test]
fn factor_of_constants() {
    let eval = |input: &str| SetChoice::Zn(7).eval(input, false, &mut Environment::new());
    assert_eq!(eval("factor(6)"), Ok("6".to_owned()));
    assert_eq!(eval("factor(7*x^2 + 3)"), Ok("3".to_owned()));
}
