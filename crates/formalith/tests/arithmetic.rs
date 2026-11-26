//! Normalization of expressions over the rationals.
use formalith::{
    field::real::R,
    parse, symbol,
    term::{Expand, Normalize, Term},
};
use malachite::Rational;

use crate::common::line;

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
    assert_eq!(line(&sqrt2), "2^(1/2)");
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

#[test]
fn products_and_sums_of_functions() {
    assert_eq!(parse!("abs(x)*abs(y)", R), parse!("abs(y)*abs(x)", R));
    assert_eq!(parse!("abs(x)+abs(y)", R), parse!("abs(y)+abs(x)", R));
    assert_eq!(parse!("abs(x)*abs(x)", R), parse!("abs(x)^2", R));
    assert_eq!(parse!("(x+1)*abs(x)", R), parse!("abs(x)*(x+1)", R));
}

fn eval_r(input: &str) -> String {
    line(&parse!(input, R))
}

#[test]
fn powers_of_zero_and_one() {
    assert_eq!(eval_r("0^0"), "1");
    assert_eq!(eval_r("x^0"), "1");
    assert_eq!(eval_r("x^1"), "x");
    assert_eq!(eval_r("0*x"), "0");
    assert_eq!(eval_r("0/x"), "0");
    assert_eq!(eval_r("x/x"), "1");
    assert_eq!(eval_r("x^2*x^(-2)"), "1");
    assert_eq!(eval_r("x^(-1/2)*x^(1/2)"), "1");
}

#[test]
fn one_to_any_power() {
    assert_eq!(eval_r("1^x"), "1");
}

#[test]
fn zero_over_zero() {
    assert_ne!(eval_r("0/0"), "0");
}

#[test]
fn sum_minus_itself() {
    assert_eq!(eval_r("(x+y)-(x+y)"), "0");
    assert_eq!(eval_r("(x+x^2)-(x+x^2)"), "0");
}

#[test]
fn reciprocal_radicals_are_merged() {
    assert_eq!(parse!("2/3*pi/sqrt(3)", R), parse!("2/9*pi*sqrt(3)", R));
    assert_eq!(parse!("1/sqrt(2)", R), parse!("sqrt(2)/2", R));
}

#[test]
fn division_by_zero_stays_unevaluated() {
    assert_eq!(eval_r("1/0"), "0^-1");
    assert_eq!(eval_r("x/0"), "x*(0^-1)");
}

#[test]
fn power_rules() {
    assert_eq!(eval_r("(x^2)^3"), "x^6");
    assert_eq!(eval_r("(x^(1/2))^2"), "x");
    assert_eq!(eval_r("(x^(1/3))^3"), "x");
    assert_eq!(eval_r("(x^3)^(1/3)"), "x");
    assert_eq!(eval_r("(x^2)^(1/2)"), "abs(x)");
    assert_eq!(eval_r("(x^2)^(1/4)"), "abs(x)^(1/2)");
    assert_eq!(eval_r("sqrt(x^4)"), "x^2");
    // Not valid for every real `x` and `a`, so kept as is
    assert_eq!(eval_r("(x^a)^b"), "(x^a)^b");
    assert_eq!(parse!("2^x*2^y", R), parse!("2^(x+y)", R));
    assert_eq!(parse!("x^a*x^b", R), parse!("x^(a+b)", R));
    assert_eq!(parse!("(x*y)^2", R), parse!("x^2*y^2", R));
    assert_eq!(parse!("(x/y)^2", R), parse!("x^2/y^2", R));
}

#[test]
fn power_is_right_associative() {
    assert_eq!(eval_r("2^3^2"), "512");
    assert_eq!(parse!("x^y^z", R), parse!("x^(y^z)", R));
}

#[test]
fn constant_radicals_are_simplified() {
    assert_eq!(parse!("sqrt(8)", R), parse!("2*sqrt(2)", R));
    assert_eq!(parse!("sqrt(12)", R), parse!("2*sqrt(3)", R));
    assert_eq!(eval_r("sqrt(1/4)"), "1/2");
    assert_eq!(parse!("sqrt(2/9)", R), parse!("sqrt(2)/3", R));
    assert_eq!(eval_r("8^(2/3)"), "4");
    assert_eq!(eval_r("4^(-1/2)"), "1/2");
    assert_eq!(parse!("sqrt(2)*sqrt(3)", R), parse!("sqrt(6)", R));
    assert_eq!(eval_r("sqrt(2)*sqrt(2)"), "2");
    assert_eq!(parse!("sqrt(2)^3", R), parse!("2*sqrt(2)", R));
    assert_eq!(eval_r("(-8)^(1/3)"), "-2");
    assert_eq!(eval_r("(-8)^(2/3)"), "4");
    assert_eq!(eval_r("(-1)^(1/3)"), "-1");
}

#[test]
fn even_roots_of_negative_constants() {
    let printed = std::panic::catch_unwind(|| eval_r("sqrt(-4)"));
    assert!(printed.is_ok(), "sqrt(-4) panicked");
    assert!(std::panic::catch_unwind(|| eval_r("(-1)^(1/2)")).is_ok());
}

#[test]
fn radicals_are_denested() {
    assert_eq!(parse!("sqrt(3+2*sqrt(2))", R), parse!("1+sqrt(2)", R));
    assert_eq!(parse!("sqrt(5+2*sqrt(6))", R), parse!("sqrt(2)+sqrt(3)", R));
}

#[test]
fn radicals_of_products() {
    assert_eq!(parse!("sqrt(4*x^2)", R), parse!("2*abs(x)", R));
    // `{$sqrt(2)$}` isn't rational, the coefficient stays inside
    assert_eq!(eval_r("sqrt(2*x)"), "(2*x)^(1/2)");
}

#[test]
fn signs_and_negations() {
    assert_eq!(eval_r("--x"), "x");
    assert_eq!(eval_r("---x"), "-x");
    assert_eq!(eval_r("-(-(-(x)))"), "-x");
    assert_eq!(eval_r("x*-1"), "-x");
    assert_eq!(eval_r("-4/-6"), "2/3");
    assert_eq!(eval_r("(x-y)+(y-x)"), "0");
    assert_eq!(eval_r("2*x+3*x-5*x"), "0");
    assert_eq!(eval_r("x/2/3"), "1/6*x");
}

#[test]
fn huge_exact_numbers() {
    assert_eq!(
        eval_r("2^200"),
        "1606938044258990275541962092341162602522202993782792835301376"
    );
    assert_eq!(eval_r("2^200/2^199"), "2");
    assert_eq!(eval_r("(10^30+1)-10^30"), "1");
    assert_eq!(eval_r("1/3^50*3^50"), "1");
}

#[test]
fn abs_sign_min_max() {
    assert_eq!(eval_r("abs(-3)"), "3");
    assert_eq!(eval_r("abs(x)^2"), "x^2");
    assert_eq!(eval_r("abs(-x)"), "abs(x)");
    assert_eq!(eval_r("abs(abs(x))"), "abs(x)");
    assert_eq!(eval_r("abs(x*y)"), "abs(x)*abs(y)");
    assert_eq!(eval_r("abs(-2*x)"), "2*abs(x)");
    assert_eq!(eval_r("sign(-2)"), "-1");
    assert_eq!(eval_r("sign(0)"), "0");
    assert_eq!(eval_r("min(3, 2)"), "2");
    assert_eq!(eval_r("max(1, 2, 3)"), "3");
    assert_eq!(eval_r("max(x, x)"), "x");
    assert_eq!(eval_r("min(x)"), "x");
}

#[test]
fn sign_symmetries() {
    assert_eq!(parse!("sign(-x)", R), parse!("-sign(x)", R));
}

#[test]
fn arithmetic_with_infinity() {
    assert_eq!(eval_r("oo - oo"), "undefined");
    assert_eq!(eval_r("oo/oo"), "undefined");
    assert_eq!(eval_r("0*oo"), "undefined");
    assert_eq!(eval_r("oo + 1"), "+oo");
    assert_eq!(eval_r("2*oo"), "+oo");
    assert_eq!(eval_r("oo*oo"), "+oo");
    assert_eq!(eval_r("-2*pi*oo"), "-oo");
    assert_eq!(eval_r("oo^-1"), "0");
    // Indeterminate powers
    assert_eq!(eval_r("oo^0"), "undefined");
    assert_eq!(eval_r("1^oo"), "undefined");
    assert_eq!(eval_r("1^(-oo)"), "undefined");
    assert_eq!(eval_r("1^undefined"), "undefined");
    assert_eq!(eval_r("undefined^0"), "undefined");
    // Symbols aren't assumed finite
    assert_eq!(eval_r("x+oo"), "oo+x");
}

#[test]
fn distributed_products_cancel() {
    assert_eq!(eval_r("(x + y) - (x + y)"), "0");
    assert_eq!(eval_r("3*(x + y) - 3*x"), "3*y");
    // Two products distributed together
    assert_eq!(eval_r("2*(x + y) - 2*(x + z)"), "2*y-2*z");
}

#[test]
fn many_products_of_sums_normalize_quickly() {
    // Trying to distribute each product `{$k (a_k + b_k)$}` normalized the other terms, which tried the others
    // again, in factorial time
    let sum = (2..=15)
        .map(|k| format!("{k}*(a_{k} + b_{k})"))
        .collect::<Vec<_>>()
        .join(" + ");
    let res = eval_r(&sum);
    assert_eq!(res.matches('(').count(), 14, "{res}");
}

#[test]
fn rationalized_denominators() {
    assert_eq!(parse!("1/(1+sqrt(2))", R), parse!("sqrt(2)-1", R));
    assert_eq!(parse!("1/(1-sqrt(2))", R), parse!("-sqrt(2)-1", R));
    assert_eq!(parse!("sqrt(2)/(sqrt(2)+1)", R), parse!("2-sqrt(2)", R));
    assert_eq!(
        parse!("(sqrt(6)-sqrt(2))/(sqrt(6)+sqrt(2))", R),
        parse!("2-sqrt(3)", R)
    );
    assert_eq!(parse!("1/(2+2*sqrt(2))", R), parse!("(sqrt(2)-1)/2", R));
    assert_eq!(parse!("x/(1+sqrt(3))", R), parse!("x*(sqrt(3)-1)/2", R));
    assert_eq!(parse!("1/(1+sqrt(2))^2", R), parse!("3-2*sqrt(2)", R));
    assert_eq!(parse!("1/(1-sqrt(2)) + 1/(1+sqrt(2))", R), rational(-2, 1));
    // Several square roots, eliminated one prime at a time
    assert_eq!(
        parse!("1/(sqrt(2)+sqrt(3)+sqrt(5))", R),
        parse!("(3*sqrt(2)+2*sqrt(3)-sqrt(30))/12", R)
    );
    assert_eq!(
        parse!(
            "(sqrt(2)+sqrt(3)+sqrt(5)+sqrt(7))*(1/(sqrt(2)+sqrt(3)+sqrt(5)+sqrt(7)))",
            R
        ),
        rational(1, 1)
    );
    // Roots of a single integer, by an inverse modulo `{$x^3 - 2$}`
    assert_eq!(
        parse!("1/(1+2^(1/3))", R),
        parse!("(1-2^(1/3)+4^(1/3))/3", R)
    );
    assert_eq!(
        parse!("1/(2^(1/3)+4^(1/3))", R),
        parse!("(2*2^(1/3)+4^(1/3)-2)/6", R)
    );
    // Bases and orders mixed, in the tower of the radicals
    assert_eq!(
        parse!("1/(sqrt(2)+3^(1/3))", R),
        parse!(
            "6-4*sqrt(2)+4*3^(1/3)+3*9^(1/3)-3*sqrt(2)*3^(1/3)-2*sqrt(2)*9^(1/3)",
            R
        )
    );
    assert_eq!(
        parse!("1/(1+6^(1/4))", R),
        parse!("(6^(1/4)-sqrt(6)+216^(1/4)-1)/5", R)
    );
    assert_eq!(
        parse!("1/(1+(2/3)^(1/3))", R),
        parse!("(3+12^(1/3)-18^(1/3))/5", R)
    );
    for x in [
        "sqrt(2)+3^(1/3)",
        "2^(1/2)+2^(1/3)",
        "1+sqrt(2)+5^(1/4)",
        "1+sqrt(2+sqrt(2))",
        "sqrt(3)+sqrt(2+sqrt(2))",
    ] {
        let x = parse!(x, R);
        assert!(!matches!(x.inv(), Term::Pow(_)), "{x}");
        assert_eq!((&x * &x.inv()).expand(), rational(1, 1), "{x}");
    }
    // Nested radicals
    assert_eq!(
        parse!("1/(1+sqrt(2+sqrt(2)))", R),
        parse!("1-sqrt(2)-sqrt(2+sqrt(2))+sqrt(2)*sqrt(2+sqrt(2))", R)
    );
}

#[test]
fn pythagorean_identity() {
    assert_eq!(parse!("sin(x)^2+cos(x)^2", R), rational(1, 1));
    assert_eq!(parse!("3*x*sin(y)^2+3*x*cos(y)^2+1", R), parse!("3*x+1", R));
    assert_eq!(
        parse!("sin(1)^2+2*cos(1)+cos(1)^2+1", R),
        parse!("2+2*cos(1)", R)
    );
    // Only pairs with the same coefficient
    assert!(matches!(parse!("2*sin(x)^2+cos(x)^2", R), Term::Add(_)));
}

#[test]
fn half_angle_roots() {
    assert_eq!(parse!("sqrt(2+2*cos(1))", R), parse!("2*cos(1/2)", R));
    assert_eq!(parse!("sqrt(1-cos(1))", R), parse!("sqrt(2)*sin(1/2)", R));
    assert_eq!(parse!("1/sqrt(2+2*cos(1))", R), parse!("1/(2*cos(1/2))", R));
    // `{$cos 2 < 0$}`
    assert_eq!(parse!("sqrt(2+2*cos(4))", R), parse!("-2*cos(2)", R));
    // Not for symbolic angles, whose sign is unknown
    assert!(matches!(parse!("sqrt(1+cos(x))", R), Term::Pow(_)));
}

#[test]
fn products_of_radical_sums_are_expanded() {
    assert_eq!(parse!("(1+sqrt(2))^2", R), parse!("3+2*sqrt(2)", R));
    assert_eq!(
        parse!("sqrt(2)*(1+sqrt(3))", R),
        parse!("sqrt(2)+sqrt(6)", R)
    );
    assert_eq!(parse!("(1+sqrt(2))*(1-sqrt(2))", R), rational(-1, 1));
    assert_eq!(parse!("(8-4*sqrt(3))/4", R), parse!("2-sqrt(3)", R));
    assert_eq!(parse!("x*(1+sqrt(3))^2", R), parse!("2*x*(2+sqrt(3))", R));
    assert_eq!(parse!("-(sqrt(2)-1)", R), parse!("1-sqrt(2)", R));
}
