//! Limits with `lim`, computed with the Gruntz algorithm, and the constants `oo` and `undefined`.
use formalith::{
    dynamic::SetChoice, field::real::R, parse, parser::environment::Environment, try_parse,
};

use crate::common::{line, typst};

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
    assert_eq!(lim("lim(1/x, x, 0, 1)"), "+oo");
    assert_eq!(lim("lim(1/x, x, 0, -1)"), "-oo");
    assert_eq!(lim("lim(1/(x-a), x, a, -1)"), "-oo");
    assert_eq!(lim("lim(abs(x)/x, x, 0, 1)"), "1");
    assert_eq!(lim("lim(abs(x)/x, x, 0, -1)"), "-1");
    assert_eq!(lim("lim(exp(-1/x), x, 0, 1)"), "0");
    assert_eq!(lim("lim(exp(-1/x), x, 0, -1)"), "+oo");
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
    assert_eq!(lim("lim(1/x^2, x, 0)"), "+oo");
}

#[test]
fn limits_at_infinity() {
    assert_eq!(lim("lim((1+1/x)^x, x, oo)"), "exp(1)");
    assert_eq!(lim("lim((1+a/x)^x, x, oo)"), "exp(a)");
    assert_eq!(lim("lim(ln(x)/x, x, oo)"), "0");
    assert_eq!(lim("lim(exp(x)/x^100, x, oo)"), "+oo");
    assert_eq!(lim("lim(x^(1/x), x, oo)"), "1");
    assert_eq!(lim("lim(x^(1/ln(x)), x, oo)"), "exp(1)");
    assert_eq!(lim("lim(2^x/3^x, x, oo)"), "0");
    assert_eq!(lim("lim((3^x + 5^x)^(1/x), x, oo)"), "5");
    assert_eq!(lim("lim(ln(x^2+1) - 2*ln(x), x, oo)"), "0");
    assert_eq!(lim("lim(ln(ln(x))/ln(x), x, oo)"), "0");
    assert_eq!(lim("lim(exp(x)/exp(x+1), x, oo)"), "exp(-1)");
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
    assert_eq!(lim("lim(x+sin(x), x, oo)"), "+oo");
    assert_eq!(lim("lim(x*(2+sin(x)), x, -oo)"), "-oo");
    assert_eq!(lim("lim(exp(x)*(2+cos(x)), x, oo)"), "+oo");
    assert_eq!(lim("lim(ln(2+sin(x))/x, x, oo)"), "0");
    assert_eq!(lim("lim(exp(-x)*sin(exp(x)), x, oo)"), "0");
    // Angles linked by `{$g_2 ~ k g_1 + d$}`
    assert_eq!(lim("lim(sin(x)^2+cos(x)^2, x, oo)"), "1");
    assert_eq!(lim("lim(sin(2*x)-2*sin(x)*cos(x), x, oo)"), "0");
    // Powers of `cos` written as sums, `{$cos(t)^2 = (1 + cos(2 t))/2$}`
    assert_eq!(lim("lim(cos(x)^2-cos(2*x)/2, x, oo)"), "1/2");
    assert_eq!(lim("lim(cos(x+pi)+cos(x), x, oo)"), "0");
}

#[test]
fn limits_of_min_max_sign() {
    assert_eq!(lim("lim(max(x, x^2)/x^2, x, oo)"), "1");
    assert_eq!(lim("lim(min(x, 1), x, 2)"), "1");
    assert_eq!(lim("lim(max(1/x, 1), x, 0, 1)"), "+oo");
    assert_eq!(lim("lim(sign(x), x, 0, 1)"), "1");
    assert_eq!(lim("lim(sign(x), x, 0, -1)"), "-1");
}

#[test]
fn limits_with_parameter_signs() {
    assert_eq!(lim("lim(a*x, x, oo)"), "oo*sign(a)");
    assert_eq!(lim("lim(-a*x, x, oo)"), "-oo*sign(a)");
    assert_eq!(lim("lim(a^2*x, x, oo)"), "+oo");
    assert_eq!(lim("lim(a/x^2, x, 0)"), "oo*sign(a)");
    // `{$sign(a) oo$}` and `{$-sign(a) oo$}` on each side
    assert_eq!(lim("lim(a/x, x, 0)"), "undefined");
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
fn limits_of_powers_of_negative_constants() {
    // `{$c^g$}` behaves like `{$|c|^g cos(pi g)$}`, not `{$exp(g ln c)$}` with `{$ln c$}` taken as real
    assert_eq!(lim("lim((-1)^x, x, oo)"), "undefined");
    assert_eq!(lim("lim((-1)^x, x, -oo)"), "undefined");
    assert_eq!(lim("lim((-2)^x, x, oo)"), "undefined");
    assert_eq!(lim("lim(x*(-1)^x, x, oo)"), "undefined");
    assert_eq!(lim("lim((-1)^(2*x), x, oo)"), "undefined");
    assert_eq!(lim("lim((-1/2)^x, x, oo)"), "0");
    assert_eq!(lim("lim((-2)^x, x, -oo)"), "0");
    assert_eq!(lim("lim((-1)^x/x, x, oo)"), "0");
    // Not continuous at finite points
    assert_eq!(lim("lim((-1)^x, x, 0)"), "lim((-1)^x, x, 0)");
}

#[test]
fn limits_of_powers_of_constants_of_unknown_sign() {
    // `{$c^g = exp(g ln c)$}` only for `{$c > 0$}`: split where `{$a + 1$}` and `{$ln|a + 1|$}` change sign
    assert_eq!(
        lim("lim(1/(a+1)^n, n, oo)"),
        "piecewise(a < -2, 0, a <= -1, undefined, a < 0, +oo, a = 0, 1, 0)"
    );
    let mut env = Environment::new();
    env.eval("assume(a < 0)", R).unwrap();
    assert_eq!(
        line(&parse!("lim(1/(a+1)^n, n, oo)", R, &env)),
        "piecewise(a < -2, 0, a <= -1, undefined, +oo)"
    );
    env.eval("assume(b > 0)", R).unwrap();
    assert_eq!(line(&parse!("lim(1/(b+1)^n, n, oo)", R, &env)), "0");
    // `{$0^g$}` is 0 when `{$lim g > 0$}`, a division by zero near the point when `{$lim g < 0$}`
    assert_eq!(lim("lim(0^n, n, oo)"), "0");
    assert_eq!(lim("lim(0^(x^2 + 1), x, oo)"), "0");
    assert_eq!(lim("lim(x + 0^(1 + x), x, 0)"), "0");
    assert_eq!(lim("lim(0^(-n), n, oo)"), "undefined");
    assert_eq!(lim("lim(0^x, x, 0)"), "lim(0^x, x, 0)");
    assert_eq!(lim("lim(2^x, x, oo)"), "+oo");
    assert_eq!(lim("lim((1/2)^x, x, oo)"), "0");
}

#[test]
fn limits_left_unevaluated() {
    // Tends to `oo` on its domain, between poles where it isn't defined, or several independent oscillations
    assert_eq!(lim("lim(x/sin(x)^2, x, oo)"), "lim(x*(sin(x)^-2), x, +oo)");
    assert_eq!(
        lim("lim(sin(x)+sin(x^2), x, oo)"),
        "lim(sin(x^2)+sin(x), x, +oo)"
    );
    // Invalid direction
    assert_eq!(lim("lim(1/x, x, 0, 2)"), "lim(x^-1, x, 0, 2)");
    assert_eq!(lim("lim(x, x, oo, 1)"), "lim(x, x, +oo, 1)");
    assert!(try_parse!("lim(x, x)", R).is_err());
}

#[test]
fn print_limits() {
    assert_eq!(
        typst(&parse!("lim(x/sin(x)^2, x, oo)", R)),
        "lim_(x -> +oo) (frac(x, sin(x)^2))"
    );
    assert_eq!(
        typst(&parse!("lim(1/(x^2*sin(1/x)^2), x, 0, -1)", R)),
        "lim_(x -> 0^-) (frac(1, x^2 sin(frac(1, x))^2))"
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
    assert_eq!(eval("x + 1 = oo"), Ok("x = +∞".to_string()));
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

#[test]
fn classic_limits() {
    assert_eq!(lim("lim((1+1/x)^x, x, oo)"), "exp(1)");
    assert_eq!(lim("lim((1+a/x)^x, x, oo)"), "exp(a)");
    assert_eq!(lim("lim((1+x)^(1/x), x, 0)"), "exp(1)");
    assert_eq!(lim("lim(x^(1/x), x, oo)"), "1");
    assert_eq!(lim("lim((sin(x)-x)/x^3, x, 0)"), "-1/6");
    assert_eq!(lim("lim((tan(x)-sin(x))/x^3, x, 0)"), "1/2");
    assert_eq!(lim("lim((1-cos(x))/x^2, x, 0)"), "1/2");
    assert_eq!(lim("lim((exp(x)-1-x)/x^2, x, 0)"), "1/2");
    assert_eq!(lim("lim(ln(1+x)/x, x, 0)"), "1");
    assert_eq!(lim("lim(asin(x)/x, x, 0)"), "1");
    assert_eq!(lim("lim((2^x-1)/x, x, 0)"), "ln(2)");
    assert_eq!(lim("lim(sin(x)^2/x, x, 0)"), "0");
    assert_eq!(lim("lim(cos(x)^(1/x^2), x, 0)"), "exp(-1/2)");
    assert_eq!(lim("lim(x^2*(1-cos(1/x)), x, oo)"), "1/2");
    assert_eq!(lim("lim(x*(atan(x)-pi/2), x, oo)"), "-1");
}

#[test]
fn limits_of_growth_rates() {
    assert_eq!(lim("lim(exp(x)/x^1000, x, oo)"), "+oo");
    assert_eq!(lim("lim(x^2*exp(-x)*ln(x)^10, x, oo)"), "0");
    assert_eq!(lim("lim(ln(ln(x))/ln(x), x, oo)"), "0");
    assert_eq!(lim("lim(exp(-1/x^2)/x^100, x, 0)"), "0");
    assert_eq!(lim("lim((3^x+5^x)^(1/x), x, oo)"), "5");
    assert_eq!(lim("lim((x^(1/x)-1)*x/ln(x), x, oo)"), "1");
    assert_eq!(lim("lim(ln(x)^ln(x)/x^ln(ln(x)), x, oo)"), "1");
    assert_eq!(lim("lim(sqrt(x)*(sqrt(x+1)-sqrt(x)), x, oo)"), "1/2");
    assert_eq!(lim("lim(sqrt(x+sqrt(x))-sqrt(x), x, oo)"), "1/2");
    assert_eq!(lim("lim((x+1)^(1/3)-x^(1/3), x, oo)"), "0");
    assert_eq!(lim("lim(x^(x^x), x, 0, 1)"), "0");
}

#[test]
fn limits_from_the_gruntz_thesis() {
    assert_eq!(lim("lim(exp(x)*(exp(1/x-exp(-x))-exp(1/x)), x, oo)"), "-1");
    assert_eq!(
        lim("lim(exp(x)*(exp(1/x+exp(-x)+exp(-x^2))-exp(1/x-exp(-exp(x)))), x, oo)"),
        "1"
    );
    assert_eq!(lim("lim(exp(exp(x))/exp(exp(x-1/x)), x, oo)"), "+oo");
    assert_eq!(
        lim("lim(exp(exp(exp(x+exp(-x))))/exp(exp(exp(x))), x, oo)"),
        "+oo"
    );
    assert_eq!(
        lim("lim(exp(exp(exp(x)))/exp(exp(exp(x-exp(-exp(x))))), x, oo)"),
        "+oo"
    );
    assert_eq!(
        lim(
            "lim(ln(x)^2*exp(sqrt(ln(x))*ln(ln(x))^2*exp(sqrt(ln(ln(x)))*ln(ln(ln(x)))^3))/sqrt(x), x, +oo)"
        ),
        "0"
    );
    assert_eq!(lim("lim((sin(tan(x))-tan(sin(x)))/x^7, x, 0)"), "-1/30");
}

#[test]
fn limits_of_special_functions() {
    assert_eq!(lim("lim(atan(x), x, -oo)"), "-1/2*pi");
    assert_eq!(lim("lim(tanh(x), x, oo)"), "1");
    assert_eq!(lim("lim(erf(x), x, -oo)"), "-1");
    assert_eq!(lim("lim(exp(x)*erf(x)-exp(x), x, oo)"), "0");
}

#[test]
fn limits_with_logarithms_of_rationals() {
    assert_eq!(lim("lim(x - ln(cosh(x)), x, oo)"), "ln(2)");
}

#[test]
fn oscillating_limits() {
    assert_eq!(lim("lim(x*sin(1/x), x, 0)"), "0");
    assert_eq!(lim("lim(sin(1/x), x, 0)"), "undefined");
    assert_eq!(lim("lim(sin(x)/x, x, oo)"), "0");
    assert_eq!(lim("lim(sin(x), x, oo)"), "undefined");
    assert_eq!(lim("lim(x*sin(x), x, oo)"), "undefined");
    assert_eq!(lim("lim(sin(x)+cos(x), x, oo)"), "undefined");
    assert_eq!(lim("lim(sin(x)/sin(x), x, oo)"), "1");
    assert_eq!(lim("lim(exp(-x)*sin(x), x, oo)"), "0");
    assert_eq!(lim("lim(exp(1/x)*sin(x)/x, x, oo)"), "0");
}

#[test]
fn two_sided_limits_that_differ() {
    assert_eq!(lim("lim(1/x, x, 0)"), "undefined");
    assert_eq!(lim("lim(abs(x)/x, x, 0)"), "undefined");
    assert_eq!(lim("lim(x/(x-1), x, 1)"), "undefined");
    assert_eq!(lim("lim(1/(x-1)^2, x, 1)"), "+oo");
    assert_eq!(lim("lim(x*ln(x), x, 0, 1)"), "0");
    assert_eq!(lim("lim(ln(x)/x, x, 0, 1)"), "-oo");
    assert_eq!(lim("lim((x^x-1)/(x*ln(x)), x, 0, 1)"), "1");
}

#[test]
fn limits_of_constants() {
    assert_eq!(lim("lim(oo, x, 0)"), "+oo");
    assert_eq!(lim("lim(undefined, x, 0)"), "undefined");
    assert_eq!(lim("lim(5, x, oo)"), "5");
    assert_eq!(lim("lim(pi, x, 0, -1)"), "pi");
}

#[test]
fn limits_with_factorials() {
    assert_eq!(lim("lim(factorial(x)^(1/x)/x, x, oo)"), "exp(-1)");
    assert_eq!(lim("lim(ln(factorial(x))/(x*ln(x)), x, oo)"), "1");
    assert_eq!(lim("lim(binomial(2*x, x)^(1/x), x, oo)"), "4");
    assert_eq!(lim("lim(gamma(x+1/2)/(sqrt(x)*gamma(x)), x, oo)"), "1");
    assert_eq!(lim("lim(x*gamma(x), x, 0)"), "1");
    assert_eq!(lim("lim(gamma(x), x, 0)"), "undefined");
}

#[test]
fn limits_of_gamma_at_minus_infinity() {
    // Poles accumulate at `-oo`
    assert_eq!(lim("lim(gamma(x), x, -oo)"), "undefined");
    assert_eq!(lim("lim(gamma(x)^2, x, -oo)"), "undefined");
    assert_eq!(lim("lim(gamma(x) + 1, x, -oo)"), "undefined");
    assert_eq!(lim("lim(1/gamma(x), x, -oo)"), "undefined");
    assert_eq!(lim("lim(gamma(x+1/2)/gamma(x), x, -oo)"), "undefined");
    assert_eq!(lim("lim(gamma(1/x), x, 0, -1)"), "undefined");
    // By the reflection formula
    assert_eq!(lim("lim(gamma(x)*sin(pi*x), x, -oo)"), "0");
    assert_eq!(lim("lim(factorial(x)*sin(pi*x), x, -oo)"), "0");
    assert_eq!(lim("lim(gamma(x)/gamma(x+1), x, -oo)"), "0");
    assert_eq!(lim("lim(x*gamma(x)/gamma(x+1), x, -oo)"), "1");
    assert_eq!(lim("lim(gamma(x)*gamma(1-x)*sin(pi*x), x, -oo)"), "pi");
    // Removable singularities of the reflected `sin(pi x)`
    assert_eq!(lim("lim(gamma(x)*sin(2*pi*x), x, -oo)"), "0");
    assert_eq!(lim("lim(exp(gamma(x)*sin(2*pi*x)), x, -oo)"), "1");
    // Arguments with their own oscillations
    assert_eq!(
        lim("lim(gamma(-x + sin(x))*sin(pi*(-x + sin(x))), x, oo)"),
        "0"
    );
}

#[test]
fn limits_with_accumulating_poles() {
    assert_eq!(lim("lim(1/(x*sin(x)), x, oo)"), "undefined");
    assert_eq!(lim("lim(tan(x), x, oo)"), "undefined");
    assert_eq!(lim("lim(1/cos(x)^2, x, oo)"), "undefined");
    assert_eq!(lim("lim(sin(x)/sin(x+1), x, oo)"), "undefined");
    // `sin(2 x)/sin(x) = 2 cos(x)`
    assert_eq!(lim("lim(sin(2*x)/sin(x), x, oo)"), "undefined");
    assert_eq!(lim("lim(sin(3*x)/(x*sin(x)), x, oo)"), "0");
}

#[test]
fn limits_with_polygamma() {
    assert_eq!(lim("lim(digamma(x) - ln(x), x, oo)"), "0");
    assert_eq!(lim("lim(x*(digamma(x) - ln(x)), x, oo)"), "-1/2");
    assert_eq!(lim("lim(x*polygamma(1, x), x, oo)"), "1");
    assert_eq!(lim("lim(digamma(x) + 1/x, x, 0)"), "-euler_gamma");
}

#[test]
fn limits_of_polygamma_at_minus_infinity() {
    // Poles accumulate at `-oo`
    assert_eq!(lim("lim(digamma(x), x, -oo)"), "undefined");
    assert_eq!(lim("lim(polygamma(1, x), x, -oo)"), "undefined");
    assert_eq!(lim("lim(polygamma(1, 1/x), x, 0, -1)"), "undefined");
    assert_eq!(lim("lim(digamma(x)/digamma(1-x), x, -oo)"), "undefined");
    assert_eq!(lim("lim(digamma(x)*sin(pi*x), x, -oo)"), "undefined");
    assert_eq!(lim("lim(polygamma(2, x)*sin(pi*x)^3, x, -oo)"), "undefined");
    // By the reflection formula `psi(1 - x) - psi(x) = pi cot(pi x)` and its derivatives
    assert_eq!(
        lim("lim((digamma(x) - digamma(1-x))*tan(pi*x), x, -oo)"),
        "-pi"
    );
    assert_eq!(lim("lim(polygamma(1, x)*sin(pi*x)^2, x, -oo)"), "pi^2");
    assert_eq!(
        lim("lim((polygamma(2, x) - polygamma(2, 1-x))*sin(pi*x)^3/cos(pi*x), x, -oo)"),
        "-2*(pi^3)"
    );
}

#[test]
fn limits_of_step_functions() {
    assert_eq!(lim("lim(floor(x), x, 1)"), "undefined");
    assert_eq!(lim("lim(floor(x), x, 1, 1)"), "1");
    assert_eq!(lim("lim(floor(x), x, 1, -1)"), "0");
    assert_eq!(lim("lim(ceil(x^2), x, 0)"), "1");
    assert_eq!(lim("lim(floor(x), x, pi)"), "3");
    assert_eq!(lim("lim(x*floor(1/x), x, oo)"), "0");
}

#[test]
fn limits_with_parameter_exponents() {
    assert_eq!(lim("lim(x^2*exp(-a^2*x), x, oo)"), "0");
}

#[test]
fn oscillations_with_a_parametric_frequency() {
    assert_eq!(lim("lim(cos(t*x)/x, x, oo)"), "0");
    assert_eq!(lim("lim(exp(-x)*sin(t*x), x, oo)"), "0");
    assert_eq!(lim("lim(cos(t*x), x, oo)"), "undefined");
}

#[test]
fn limits_of_exponential_integrals() {
    assert_eq!(lim("lim(Si(x), x, oo)"), "1/2*pi");
    assert_eq!(lim("lim(Si(x), x, -oo)"), "-1/2*pi");
    assert_eq!(lim("lim(Ci(x), x, oo)"), "0");
    assert_eq!(lim("lim(Ci(abs(x)), x, -oo)"), "0");
    assert_eq!(lim("lim(Ei(x), x, -oo)"), "0");
    // `{$"Ei"(x) ~ e^x / x$}`
    assert_eq!(lim("lim(Ei(x)*x*exp(-x), x, oo)"), "1");
    // `{$pi/2 - "Si"(x) ~ cos(x) / x$}` oscillates
    assert_eq!(lim("lim(x*(pi/2 - Si(x)), x, oo)"), "undefined");
    assert_eq!(lim("lim(Si(x)/x, x, 0)"), "1");
    assert_eq!(lim("lim(Ci(x) - ln(x), x, 0, 1)"), "euler_gamma");
    assert_eq!(lim("lim(Ei(x) - ln(abs(x)), x, 0)"), "euler_gamma");
    assert_eq!(lim("lim(Si(x), x, 2)"), "Si(2)");
}
