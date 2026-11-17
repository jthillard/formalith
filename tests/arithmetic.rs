//! Normalization of expressions over the rationals.
use formalith::{
    field::real::R,
    parse, symbol,
    term::{Normalize, Term},
};
use malachite::Rational;

mod common;
use common::line;

fn rational(num: i64, den: i64) -> Term<R<Rational>> {
    Rational::from_signeds(num, den).into()
}

#[test]
fn constants_are_evaluated() {
    assert_eq!(parse!("2+3*4", R), 14.into());
    assert_eq!(parse!("(2+3)*4", R), 20.into());
    assert_eq!(parse!("2-3-4", R), (-5).into());
    assert_eq!(parse!("2/3/4", R), rational(1, 6));
    assert_eq!(parse!("1/2*3", R), rational(3, 2));
    assert_eq!(parse!("1/3*3", R), 1.into());
    assert_eq!(parse!("1/3+1/6", R), rational(1, 2));
    assert_eq!(parse!("0.1+0.2", R), rational(3, 10));
    assert_eq!(parse!("0.5+0.25", R), rational(3, 4));
    assert_eq!(parse!("2*-3", R), (-6).into());
    assert_eq!(parse!("3--3", R), 6.into());
    assert_eq!(parse!("007", R), 7.into());
}

#[test]
fn constant_powers() {
    assert_eq!(parse!("5.5^2", R), rational(121, 4));
    assert_eq!(parse!("2^-1", R), rational(1, 2));
    assert_eq!(parse!("2^-3", R), rational(1, 8));
    assert_eq!(parse!("(-2)^2", R), 4.into());
    assert_eq!(parse!("(-2)^3", R), (-8).into());
    assert_eq!(parse!("-2^2", R), (-4).into());
    assert_eq!(parse!("4^(1/2)", R), 2.into());
    assert_eq!(parse!("8^(1/3)", R), 2.into());
    assert_eq!(parse!("(4/9)^(1/2)", R), rational(2, 3));
    assert_eq!(parse!("0^0", R), 1.into());
    assert_eq!(parse!("1^100", R), 1.into());
}

#[test]
fn irrational_powers_stay_symbolic() {
    let sqrt2 = parse!("2^(1/2)", R);
    assert!(matches!(sqrt2, Term::Pow(_)));
    assert_eq!(line(&sqrt2), "2^1/2");
}

#[test]
fn big_numbers() {
    assert_eq!(
        line(&parse!(
            "100000000000000000000000000*100000000000000000000",
            R
        )),
        "10000000000000000000000000000000000000000000000"
    );
    assert_eq!(line(&parse!("2^100", R)), "1267650600228229401496703205376");
}

#[test]
fn neutral_and_absorbing_elements() {
    let x = parse!("x", R);
    assert_eq!(parse!("x+0", R), x);
    assert_eq!(parse!("0+x", R), x);
    assert_eq!(parse!("x*1", R), x);
    assert_eq!(parse!("1*x", R), x);
    assert_eq!(parse!("x^1", R), x);
    assert_eq!(parse!("x/1", R), x);
    assert_eq!(parse!("x*0", R), 0.into());
    assert_eq!(parse!("0*x*y", R), 0.into());
    assert_eq!(parse!("x^0", R), 1.into());
    assert_eq!(parse!("(x+y)^0", R), 1.into());
}

#[test]
fn like_terms_are_merged() {
    assert_eq!(parse!("x-x", R), 0.into());
    assert_eq!(parse!("x+x", R), parse!("2*x", R));
    assert_eq!(parse!("2*x+3*x", R), parse!("5*x", R));
    assert_eq!(parse!("x/2+x/3", R), parse!("5/6*x", R));
    assert_eq!(parse!("x+y-x", R), parse!("y", R));
    assert_eq!(parse!("x*y-y*x", R), 0.into());
    assert_eq!(parse!("2*x*y+3*y*x", R), parse!("5*x*y", R));
}

#[test]
fn like_factors_are_merged() {
    assert_eq!(parse!("x*x", R), parse!("x^2", R));
    assert_eq!(parse!("x^2*x^3", R), parse!("x^5", R));
    assert_eq!(parse!("x^2*x", R), parse!("x^3", R));
    assert_eq!(parse!("x/x", R), 1.into());
    assert_eq!(parse!("x^2/x", R), parse!("x", R));
    assert_eq!(parse!("x^(-1)*x", R), 1.into());
    assert_eq!(parse!("x^a*x^b", R), parse!("x^(a+b)", R));
    assert_eq!(parse!("2^x*2^y", R), parse!("2^(x+y)", R));
}

#[test]
fn nested_powers() {
    assert_eq!(parse!("(x^2)^3", R), parse!("x^6", R));
    assert_eq!(parse!("(x^-1)^-1", R), parse!("x", R));
    // Symbolic exponents are not merged, since `(x^n)^m != x^(n*m)` in general
    assert!(matches!(parse!("(x^n)^m", R), Term::Pow(_)));
}

#[test]
fn commutativity_and_associativity() {
    assert_eq!(parse!("x+y", R), parse!("y+x", R));
    assert_eq!(parse!("x*y", R), parse!("y*x", R));
    assert_eq!(parse!("(x+y)+z", R), parse!("x+(y+z)", R));
    assert_eq!(parse!("(x*y)*z", R), parse!("x*(y*z)", R));
    assert_eq!(parse!("x+y+z", R), parse!("z+y+x", R));
    assert_eq!(parse!("x*y*z", R), parse!("z*x*y", R));
    assert_eq!(parse!("1+x+2", R), parse!("x+3", R));
    assert_eq!(parse!("2*x*3", R), parse!("6*x", R));
}

#[test]
fn double_negation() {
    assert_eq!(parse!("-(-(x))", R), parse!("x", R));
    assert_eq!(parse!("-+-+--5", R), 5.into());
}

#[test]
fn normalize_is_idempotent() {
    for input in [
        "x",
        "x+y*2",
        "(x+1)^2*y",
        "x^-1+y^-2",
        "1/(x+1)+1/(x-1)",
        "2^(1/2)*x",
    ] {
        let term = parse!(input, R);
        assert_eq!(term.normalize(), term, "{input}");
    }
}

#[test]
fn operators_on_terms() {
    let x = parse!("x", R);
    let y = parse!("y", R);
    assert_eq!(&x + &y, parse!("x+y", R));
    assert_eq!(&x - &y, parse!("x-y", R));
    assert_eq!(&x * &y, parse!("x*y", R));
    assert_eq!(&x / &y, parse!("x/y", R));
    assert_eq!(-&x, parse!("-x", R));
    assert_eq!(&x - &x, 0.into());
    assert_eq!(&x / &x, 1.into());
    assert_eq!(x.clone() * x.clone(), parse!("x^2", R));
    assert_eq!(x.pow(&2.into()), parse!("x^2", R));
    assert_eq!(parse!("x+1", R).pow(&2.into()), parse!("(x+1)^2", R));
    assert_eq!(x.inv(), parse!("x^-1", R));
    assert_eq!(parse!("2", R).inv(), rational(1, 2));
    assert_eq!(parse!("2/3", R).inv(), rational(3, 2));
}

#[test]
fn zero_and_one() {
    assert!(Term::zero(R).is_zero());
    assert!(Term::one(R).is_one());
    assert!(parse!("0", R).is_zero());
    assert!(parse!("x-x", R).is_zero());
    assert!(!parse!("x", R).is_zero());
    assert!(!parse!("1", R).is_zero());
    assert!(parse!("1", R).is_one());
    assert!(parse!("x/x", R).is_one());
    assert!(!parse!("x", R).is_one());
    assert!(!parse!("2", R).is_one());
}

#[test]
fn sign_checks() {
    assert!(parse!("3", R).is_strictly_positive());
    assert!(parse!("3", R).is_positive());
    assert!(!parse!("3", R).is_negative());
    assert!(parse!("-3", R).is_strictly_negative());
    assert!(parse!("-1/2", R).is_negative());
    assert!(parse!("0", R).is_positive());
    assert!(parse!("0", R).is_negative());
    assert!(!parse!("0", R).is_strictly_positive());
    assert!(!parse!("0", R).is_strictly_negative());
    // Unknown sign
    assert!(!parse!("x", R).is_positive());
    assert!(!parse!("x", R).is_negative());
}

#[test]
fn compare_terms() {
    use std::cmp::Ordering;
    assert_eq!(parse!("1", R).cmp(&parse!("2", R)), Ordering::Less);
    assert_eq!(parse!("2", R).cmp(&parse!("1", R)), Ordering::Greater);
    assert_eq!(parse!("x", R).cmp(&parse!("x", R)), Ordering::Equal);
    assert_eq!(parse!("3", R).cmp(&parse!("x", R)), Ordering::Greater);
}

#[test]
fn symbols() {
    assert_eq!(symbol!("foo"), symbol!("foo"));
    assert_ne!(symbol!("foo"), symbol!("bar"));
    assert_eq!(parse!("foo", R), symbol!("foo", R));
    assert_eq!(parse!("x_1", R), symbol!("x_1", R));
    assert_ne!(parse!("x1", R), parse!("x", R));
    assert_ne!(parse!("xy", R), parse!("x*y", R));
}

#[test]
fn abs_of_symbol_stays_unevaluated() {
    let abs = parse!("abs(x)", R);
    assert!(matches!(abs, Term::Fun(_)));
    assert_eq!(line(&abs), "abs(x)");
}

#[test]
fn abs_of_constants() {
    assert_eq!(parse!("abs(-5)", R), 5.into());
    assert_eq!(parse!("abs(5)", R), 5.into());
    assert_eq!(parse!("abs(0)", R), 0.into());
    assert_eq!(parse!("abs(-1/2)", R), rational(1, 2));
    assert_eq!(parse!("2*abs(3)", R), 6.into());
}

#[test]
fn det_of_constant_matrices() {
    assert_eq!(parse!("det([[1,2],[3,4]])", R), (-2).into());
    assert_eq!(parse!("det([[5]])", R), 5.into());
    assert_eq!(parse!("det(5)", R), 5.into());
    assert_eq!(parse!("det([[1,2,3],[4,5,6],[7,8,10]])", R), (-3).into());
    assert_eq!(parse!("det([[1,2],[2,4]])", R), 0.into());
    assert_eq!(parse!("det([[x,4],[2,3]])", R), parse!("3*x-8", R));
}

#[test]
fn abs_of_symbol() {
    assert!(!parse!("abs(x)", R).is_one());
    let _ = parse!("2*abs(x)", R);
    let _ = parse!("abs(x)", R).simplify();
}

#[test]
fn division_by_zero_does_not_panic() {
    let _ = formalith::try_parse!("1/0", R);
    let _ = formalith::try_parse!("0^-1", R);
}

#[test]
fn det_with_row_swap() {
    assert_eq!(parse!("det([[0,1,0],[1,0,0],[0,0,1]])", R), (-1).into());
    assert_eq!(parse!("det([[0,1,2],[1,0,3],[4,-3,8]])", R), (-2).into());
}

#[test]
fn operators_after_function_call() {
    assert_eq!(parse!("abs(3)*2", R), 6.into());
    assert_eq!(parse!("abs(3)+abs(4)", R), 7.into());
    assert_eq!(parse!("abs(3)*abs(-3)", R), 9.into());
    assert_eq!(parse!("abs(3)^2", R), 9.into());
    assert_eq!(parse!("abs(-2)*x", R), parse!("2*x", R));
    assert_eq!(parse!("det([[1]])*det([[2]])", R), 2.into());
}

#[test]
fn function_call_as_right_operand() {
    assert_eq!(parse!("x*abs(-3)", R), parse!("3*x", R));
    assert_eq!(parse!("x+abs(-3)", R), parse!("x+3", R));
}

#[test]
fn negative_exponent_precedence() {
    assert_eq!(parse!("x^-1*x", R), 1.into());
    assert_eq!(parse!("2^-1*4", R), 2.into());
}
