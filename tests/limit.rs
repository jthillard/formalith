//! Limits with `lim`, computed with the Gruntz algorithm, and the constants `oo` and `undefined`.
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
fn limits_of_oscillating_functions() {
    assert_eq!(lim("lim(sin(x)/x, x, oo)"), "0");
    assert_eq!(lim("lim(x*sin(1/x), x, 0)"), "0");
    assert_eq!(lim("lim((x+sin(x))/x, x, oo)"), "1");
    assert_eq!(lim("lim(x/(x+sin(x)), x, oo)"), "1");
    assert_eq!(lim("lim(x+sin(x), x, oo)"), "oo");
    assert_eq!(lim("lim(x*(2+sin(x)), x, -oo)"), "-oo");
    assert_eq!(lim("lim(exp(x)*(2+cos(x)), x, oo)"), "oo");
    assert_eq!(lim("lim(ln(2+sin(x))/x, x, oo)"), "0");
    assert_eq!(lim("lim(exp(-x)*sin(exp(x)), x, oo)"), "0");
    // Angles linked by `{$g_2 ~ k g_1 + d$}`
    assert_eq!(lim("lim(sin(x)^2+cos(x)^2, x, oo)"), "1");
    assert_eq!(lim("lim(sin(2*x)-2*sin(x)*cos(x), x, oo)"), "0");
    assert_eq!(lim("lim(cos(x+pi)+cos(x), x, oo)"), "0");
}

#[test]
fn limits_of_min_max_sign() {
    assert_eq!(lim("lim(max(x, x^2)/x^2, x, oo)"), "1");
    assert_eq!(lim("lim(min(x, 1), x, 2)"), "1");
    assert_eq!(lim("lim(max(1/x, 1), x, 0, 1)"), "oo");
    assert_eq!(lim("lim(sign(x), x, 0, 1)"), "1");
    assert_eq!(lim("lim(sign(x), x, 0, -1)"), "-1");
}

#[test]
fn limits_with_parameter_signs() {
    assert_eq!(lim("lim(a*x, x, oo)"), "oo*sign(a)");
    assert_eq!(lim("lim(-a*x, x, oo)"), "-oo*sign(a)");
    assert_eq!(lim("lim(a^2*x, x, oo)"), "oo");
    assert_eq!(lim("lim(a/x^2, x, 0)"), "oo*sign(a)");
}

#[test]
fn undefined_limits() {
    // Both sides differ
    assert_eq!(lim("lim(1/x, x, 0)"), "undefined");
    assert_eq!(lim("lim(abs(x)/x, x, 0)"), "undefined");
    assert_eq!(lim("lim(sign(x), x, 0)"), "undefined");
    assert_eq!(lim("lim(a/x, x, 0)"), "undefined");
    // Oscillations
    assert_eq!(lim("lim(sin(x), x, oo)"), "undefined");
    assert_eq!(lim("lim(sin(1/x), x, 0)"), "undefined");
    assert_eq!(lim("lim(x*sin(x), x, oo)"), "undefined");
    assert_eq!(lim("lim(1/(2+sin(x)), x, oo)"), "undefined");
    assert_eq!(lim("lim(sin(x+1)-sin(x), x, oo)"), "undefined");
}

#[test]
fn limits_left_unevaluated() {
    // Unbounded near the zeros of `sin`, or several independent oscillations
    assert_eq!(
        lim("lim(1/(x*sin(x)), x, oo)"),
        "lim((x^-1)*(sin(x)^-1), x, oo)"
    );
    assert_eq!(
        lim("lim(sin(x)+sin(x^2), x, oo)"),
        "lim(sin(x^2)+sin(x), x, oo)"
    );
    // Invalid direction
    assert_eq!(lim("lim(1/x, x, 0, 2)"), "lim(x^-1, x, 0, 2)");
    assert_eq!(lim("lim(x, x, oo, 1)"), "lim(x, x, oo, 1)");
    assert!(try_parse!("lim(x, x)", R).is_err());
}

#[test]
fn print_limits() {
    assert_eq!(
        typst(&parse!("lim(1/(x*sin(x)), x, oo)", R)),
        "lim_(x -> oo) (frac(1, x sin(x)))"
    );
    assert_eq!(
        typst(&parse!("lim(1/(x*sin(1/x)), x, 0, -1)", R)),
        "lim_(x -> 0^-) (frac(1, x sin(frac(1, x))))"
    );
    assert_eq!(
        typst(&parse!("lim(1/x, x, 0, 2)", R)),
        "op(\"lim\")(frac(1, x), x, 0, 2)"
    );
    assert_eq!(typst(&parse!("-oo", R)), "-oo");
    assert_eq!(typst(&parse!("lim(1/x, x, 0)", R)), "\"undefined\"");
}

#[test]
fn infinity_is_a_constant() {
    let eval = |input| SetChoice::R.eval(input, false, &mut Environment::new());
    assert!(eval("oo := 1").is_err());
    assert!(eval("undefined := 1").is_err());
    assert_eq!(eval("x + 1 = oo"), Ok("x = ∞ - 1".to_string()));
}

#[test]
fn limits_of_classic_functions() {
    assert_eq!(parse!("lim(atan(x), x, oo)", R), parse!("pi/2", R));
    assert_eq!(parse!("lim(atan(x), x, -oo)", R), parse!("-pi/2", R));
    assert_eq!(lim("lim(atan(x)/x, x, 0)"), "1");
    assert_eq!(lim("lim(asin(x)/x, x, 0)"), "1");
    assert_eq!(lim("lim(acos(x), x, 1, -1)"), "0");
    assert_eq!(lim("lim(x*(pi/2 - atan(x)), x, oo)"), "1");
    assert_eq!(lim("lim(tanh(x), x, oo)"), "1");
    assert_eq!(lim("lim(tanh(x), x, -oo)"), "-1");
    assert_eq!(lim("lim(sinh(x)/exp(x), x, oo)"), "1/2");
    assert_eq!(lim("lim(asinh(x)/ln(x), x, oo)"), "1");
    assert_eq!(lim("lim(atanh(x)/x, x, 0)"), "1");
    assert_eq!(lim("lim(sec(x), x, 0)"), "1");
    assert_eq!(lim("lim(atan(sin(x)), x, oo)"), "undefined");
}
