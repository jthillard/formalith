//! Limits with `lim`, computed with the Gruntz algorithm, and the constant `oo`.
use formalith::{
    field::real::R, parse, parser::environment::Environment, repl::SetChoice, try_parse,
};

mod common;
use common::{line, typst};

fn lim(input: &str) -> String {
    line(&parse!(input, R))
}

#[test]
fn limits_of_rational_functions() {
    assert_eq!(lim("lim((x^2-1)/(x-1), x, 1)"), "2");
    assert_eq!(lim("lim((2*x^2+1)/(x^2-3), x, oo)"), "2");
    assert_eq!(lim("lim(x^3-x, x, -oo)"), "-oo");
    assert_eq!(lim("lim((x^2+1)^(1/2)/x, x, -oo)"), "-1");
    assert_eq!(lim("lim(x*(sqrt(x^2+1) - x), x, oo)"), "1/2");
    assert_eq!(lim("lim(sqrt(x^2+x) - x, x, oo)"), "1/2");
}

#[test]
fn limits_by_substitution() {
    assert_eq!(lim("lim(x^2 + 3, x, 2)"), "7");
    assert_eq!(lim("lim(x + a, x, b)"), "a+b");
    assert_eq!(lim("lim(y, x, 0)"), "y");
}

#[test]
fn one_sided_limits() {
    assert_eq!(lim("lim(1/x, x, 0, 1)"), "oo");
    assert_eq!(lim("lim(1/x, x, 0, -1)"), "-oo");
    assert_eq!(lim("lim(1/(x-a), x, a, -1)"), "-oo");
    assert_eq!(lim("lim(abs(x)/x, x, 0, 1)"), "1");
    assert_eq!(lim("lim(abs(x)/x, x, 0, -1)"), "-1");
    assert_eq!(lim("lim(exp(-1/x), x, 0, 1)"), "0");
    assert_eq!(lim("lim(exp(-1/x), x, 0, -1)"), "oo");
    assert_eq!(lim("lim(ln(x), x, 0, 1)"), "-oo");
    assert_eq!(lim("lim(x^x, x, 0, 1)"), "1");
    assert_eq!(lim("lim(x*ln(x), x, 0, 1)"), "0");
}

#[test]
fn limits_at_zero() {
    assert_eq!(lim("lim(sin(x)/x, x, 0)"), "1");
    assert_eq!(lim("lim(tan(x)/x, x, 0)"), "1");
    assert_eq!(lim("lim((1-cos(x))/x^2, x, 0)"), "1/2");
    assert_eq!(lim("lim((sin(x)-x)/x^3, x, 0)"), "-1/6");
    assert_eq!(lim("lim((exp(x)-1-x)/x^2, x, 0)"), "1/2");
    assert_eq!(lim("lim(1/x^2, x, 0)"), "oo");
}

#[test]
fn limits_at_infinity() {
    assert_eq!(lim("lim((1+1/x)^x, x, oo)"), "exp(1)");
    assert_eq!(lim("lim((1+a/x)^x, x, oo)"), "exp(a)");
    assert_eq!(lim("lim(ln(x)/x, x, oo)"), "0");
    assert_eq!(lim("lim(exp(x)/x^100, x, oo)"), "oo");
    assert_eq!(lim("lim(x^(1/x), x, oo)"), "1");
    assert_eq!(lim("lim(x^(1/ln(x)), x, oo)"), "exp(1)");
    assert_eq!(lim("lim(2^x/3^x, x, oo)"), "0");
    assert_eq!(lim("lim((3^x + 5^x)^(1/x), x, oo)"), "5");
    assert_eq!(lim("lim(ln(x^2+1) - 2*ln(x), x, oo)"), "0");
    assert_eq!(lim("lim(ln(ln(x))/ln(x), x, oo)"), "0");
    assert_eq!(lim("lim(exp(x)/exp(x+1), x, oo)"), "exp(1)^-1");
}

#[test]
fn limits_of_nested_exponentials() {
    // Examples of Gruntz's thesis, where series in `x` fail
    assert_eq!(
        lim("lim(exp(x)*(exp(1/x - exp(-x)) - exp(1/x)), x, oo)"),
        "-1"
    );
    assert_eq!(
        lim("lim(exp(x)*(sin(1/x + exp(-x)) - sin(1/x)), x, oo)"),
        "1"
    );
    assert_eq!(
        lim("lim(exp(exp(x))*(exp(sin(1/x + exp(-exp(x)))) - exp(sin(1/x))), x, oo)"),
        "1"
    );
    assert_eq!(
        lim("lim(x*ln(x)*ln(x*exp(x)-x^2)^2/ln(ln(x^2+2*exp(exp(3*x^3*ln(x))))), x, oo)"),
        "1/3"
    );
}

#[test]
fn limits_left_unevaluated() {
    // Both sides differ
    assert_eq!(lim("lim(1/x, x, 0)"), "lim(x^-1, x, 0)");
    assert_eq!(lim("lim(abs(x)/x, x, 0)"), "lim((x^-1)*abs(x), x, 0)");
    // Oscillation, or a sign depending on a parameter
    assert_eq!(lim("lim(sin(x), x, oo)"), "lim(sin(x), x, oo)");
    assert_eq!(lim("lim(a*x, x, oo)"), "lim(x*a, x, oo)");
    // Invalid direction
    assert_eq!(lim("lim(1/x, x, 0, 2)"), "lim(x^-1, x, 0, 2)");
    assert!(try_parse!("lim(x, x)", R).is_err());
}

#[test]
fn print_limits() {
    assert_eq!(
        typst(&parse!("lim(1/x, x, 0)", R)),
        "lim_(x -> 0) (frac(1, x))"
    );
    assert_eq!(
        typst(&parse!("lim(a/x, x, 0, -1)", R)),
        "lim_(x -> 0^-) (frac(a, x))"
    );
    assert_eq!(
        typst(&parse!("lim(1/x, x, 0, 2)", R)),
        "op(\"lim\")(frac(1, x), x, 0, 2)"
    );
    assert_eq!(
        typst(&parse!("lim(sin(x), x, oo)", R)),
        "lim_(x -> oo) (sin(x))"
    );
    assert_eq!(typst(&parse!("-oo", R)), "-oo");
}

#[test]
fn infinity_is_a_constant() {
    let eval = |input| SetChoice::R.eval(input, false, &mut Environment::new());
    assert!(eval("oo := 1").is_err());
    assert_eq!(eval("x + 1 = oo"), Ok("x = oo - 1".to_string()));
}
