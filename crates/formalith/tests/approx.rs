//! Numerical approximation with `approx`, and the transcendental functions and constants it evaluates.
use formalith::{
    dynamic::SetChoice, field::real::R, parse, parser::environment::Environment, try_parse,
};

use crate::common::{line, pretty, typst};

fn approx(input: &str) -> String {
    line(&parse!(input, R))
}

fn eval(input: &str) -> Result<String, String> {
    SetChoice::R.eval(input, false, &mut Environment::new())
}

#[test]
fn approx_constants() {
    assert_eq!(approx("approx(sqrt(2))"), "1.4142135623731");
    assert_eq!(approx("approx(pi)"), "3.14159265358979");
    assert_eq!(
        approx("approx(pi, 50)"),
        "3.1415926535897932384626433832795028841971693993751"
    );
    assert_eq!(approx("approx(e)"), "2.71828182845905");
    assert_eq!(approx("approx(1/3)"), "0.333333333333333");
    assert_eq!(approx("approx(1)"), "1.0");
    assert_eq!(approx("approx(2^(1/3))"), "1.25992104989487");
    assert_eq!(approx("approx((-8)^(1/3))"), "-2.0");
    assert_eq!(approx("approx(2^pi)"), "8.82497782707629");
    assert_eq!(approx("approx(sqrt(2), 3)"), "1.41");
}

#[test]
fn approx_functions() {
    assert_eq!(approx("approx(exp(1))"), "2.71828182845905");
    assert_eq!(approx("approx(ln(2))"), "0.693147180559945");
    assert_eq!(approx("approx(sin(pi/6))"), "0.5");
    assert_eq!(approx("approx(cos(pi))"), "-1.0");
    assert_eq!(approx("approx(tan(1))"), "1.5574077246549");
    assert_eq!(approx("approx(sin(pi))"), "0.0");
    assert_eq!(approx("approx(floor(100*pi))"), "314.0");
    // `ln(-1)` isn't real
    assert_eq!(approx("approx(ln(-1))"), "ln(-1.0)");
}

#[test]
fn approx_keeps_significant_digits() {
    assert_eq!(approx("approx(exp(-50))"), "1.92874984796392e-22");
    // Below the first working precision
    assert_eq!(approx("approx(exp(-70))"), "3.97544973590865e-31");
    assert_eq!(approx("approx(e^(-100))"), "3.72007597602084e-44");
    assert_eq!(approx("approx(exp(100))"), "2.68811714181614e43");
    assert_eq!(approx("approx(10^20/7)"), "1.42857142857143e19");
    assert_eq!(approx("approx(1/7, 3)"), "0.143");
    assert_eq!(approx("approx(0.000001234)"), "1.234e-6");
}

#[test]
fn approx_keeps_symbols() {
    assert_eq!(approx("approx(x + sqrt(2))"), "x+1.4142135623731");
    assert_eq!(approx("approx(e*x)"), "2.71828182845905*x");
    assert_eq!(approx("approx(-sqrt(3)*x)"), "-1.73205080756888*x");
    assert_eq!(approx("approx(pi*x, 5)"), "3.1416*x");
    assert_eq!(approx("approx(x^2)"), "x^2");
    assert_eq!(approx("approx(x)"), "x");
}

#[test]
fn approximations_are_contagious() {
    assert_eq!(approx("approx(sqrt(2)) + 1"), "2.4142135623731");
    assert_eq!(approx("2*approx(sqrt(2))"), "2.8284271247462");
    assert_eq!(approx("approx(2)^(1/2)"), "1.4142135623731");
    assert_eq!(approx("sin(approx(1))"), "0.841470984807897");
    assert_eq!(approx("approx(sqrt(2))*x + x"), "2.4142135623731*x");
    // Exact values are kept exact
    assert_eq!(approx("sqrt(2) + 1"), "2^(1/2)+1");
}

#[test]
fn approx_printing() {
    assert_eq!(pretty(&parse!("approx(sqrt(2))*x", R)), "1.4142135623731⋅x");
    assert_eq!(typst(&parse!("approx(sqrt(2))*x", R)), "1.4142135623731 x");
    assert_eq!(
        typst(&parse!("approx(exp(100))", R)),
        "2.68811714181614 times 10^(43)"
    );
}

#[test]
fn approx_errors() {
    assert!(try_parse!("approx()", R).is_err());
    assert!(try_parse!("approx(1, 2, 3)", R).is_err());
    // Invalid precisions are not evaluated
    assert_eq!(approx("approx(2, 0)"), "approx(2, 0)");
    assert_eq!(approx("approx(2, 1/2)"), "approx(2, 1/2)");
}

#[test]
fn exact_values() {
    assert_eq!(parse!("exp(0)", R), parse!("1", R));
    assert_eq!(parse!("ln(1)", R), parse!("0", R));
    assert_eq!(parse!("ln(e)", R), parse!("1", R));
    assert_eq!(parse!("sin(0) + tan(0)", R), parse!("0", R));
    assert_eq!(parse!("cos(0)", R), parse!("1", R));
    assert_eq!(approx("exp(1)"), "exp(1)");
    assert_eq!(approx("pi"), "pi");
    assert_eq!(typst(&parse!("sin(x)/ln(x)", R)), "frac(sin(x), ln(x))");
}

#[test]
fn derivatives() {
    assert_eq!(parse!("diff(exp(2*x), x)", R), parse!("2*exp(2*x)", R));
    assert_eq!(parse!("diff(ln(x), x)", R), parse!("1/x", R));
    assert_eq!(parse!("diff(sin(x^2), x)", R), parse!("2*x*cos(x^2)", R));
    assert_eq!(parse!("diff(cos(x), x)", R), parse!("-sin(x)", R));
    assert_eq!(parse!("diff(tan(x), x)", R), parse!("1 + tan(x)^2", R));
    assert_eq!(parse!("diff(pi*x, x)", R), parse!("pi", R));
}

#[test]
fn constants_are_reserved() {
    assert_eq!(
        eval("pi(1)"),
        Err("Function pi expects 0 arguments, found 1".to_owned())
    );
    assert_eq!(
        eval("pi := 3"),
        Err("`pi` is a builtin constant".to_owned())
    );
    assert_eq!(
        eval("f(e) := e"),
        Err("`e` is a builtin constant".to_owned())
    );
    // Solved for `x` only
    assert!(eval("x + pi = 0").is_ok_and(|solution| solution.starts_with("x = ")));
    assert_eq!(
        eval("solve(x = pi, pi)"),
        Err("`pi` is a builtin constant, not an unknown".to_owned())
    );
}

#[test]
fn approx_classic_functions() {
    assert_eq!(approx("approx(4*atan(1))"), "3.14159265358979");
    assert_eq!(approx("approx(atan(10))"), "1.47112767430373");
    assert_eq!(approx("approx(atan(-3))"), "-1.24904577239825");
    assert_eq!(approx("approx(asin(1/3))"), "0.339836909454122");
    assert_eq!(approx("approx(asin(-1/3))"), "-0.339836909454122");
    assert_eq!(approx("approx(acos(-1/3))"), "1.91063323624902");
    assert_eq!(approx("approx(sinh(1))"), "1.1752011936438");
    assert_eq!(approx("approx(cosh(1))"), "1.54308063481524");
    assert_eq!(approx("approx(tanh(-2))"), "-0.964027580075817");
    assert_eq!(approx("approx(asinh(-1))"), "-0.881373587019543");
    assert_eq!(approx("approx(acosh(2))"), "1.31695789692482");
    assert_eq!(approx("approx(atanh(1/2))"), "0.549306144334055");
    assert_eq!(approx("approx(sec(1))"), "1.85081571768093");
    assert_eq!(approx("approx(log(2))"), "0.301029995663981");
    assert_eq!(approx("approx(factorial(10))"), "3628800.0");
    // Outside of their domain
    assert_eq!(approx("approx(asin(2))"), "asin(2.0)");
    assert_eq!(approx("approx(atanh(1))"), "atanh(1.0)");
}

#[test]
fn approx_precision_edge_cases() {
    assert_eq!(approx("approx(pi, 1)"), "3.0");
    assert_eq!(approx("approx(1/3, 3)"), "0.333");
    assert_eq!(approx("approx(0)"), "0.0");
    assert_eq!(approx("approx(-e)"), "-2.71828182845905");
    assert_eq!(
        approx("approx(pi, 50)"),
        "3.1415926535897932384626433832795028841971693993751"
    );
    assert_eq!(
        approx("approx(sqrt(2), 40)"),
        "1.41421356237309504880168872420969807857"
    );
    // Invalid numbers of digits stay unevaluated
    assert_eq!(approx("approx(pi, 0)"), "approx(pi, 0)");
    assert_eq!(approx("approx(pi, -1)"), "approx(pi, -1)");
    assert_eq!(approx("approx(pi, x)"), "approx(pi, x)");
}

#[test]
fn approx_large_and_small_magnitudes() {
    assert_eq!(approx("approx(10^20)"), "1.0e20");
    assert_eq!(approx("approx(10^-20)"), "1.0e-20");
    assert_eq!(approx("approx(e^100)"), "2.68811714181614e43");
    assert_eq!(approx("approx(ln(10^-30))"), "-69.0775527898214");
    // Needs about 10 more digits of pi to reduce the argument
    assert_eq!(approx("approx(sin(10^10))"), "-0.487506025087511");
    // Below the absolute precision, but exact or with their relative precision
    assert_eq!(approx("approx(1/factorial(700))"), "4.12875075759988e-1690");
    assert_eq!(approx("approx(exp(-5000))"), "3.36969414830892e-2172");
    assert_eq!(
        approx("approx(exp(-3000) - exp(-3001))"),
        "8.26711931498293e-1304"
    );
    assert_eq!(approx("approx((10^(-6000))^(1/3))"), "1.0e-2000");
    // Huge values are rounded and printed in integer arithmetic
    assert_eq!(
        approx("approx(gamma(10^5 + 1/3))"),
        "1.31088971180922e456570"
    );
    assert_eq!(
        approx("approx(1/gamma(10^5 + 1/3))"),
        "7.62840680639607e-456571"
    );
}

#[test]
fn approx_near_integers_and_cancellations() {
    // Ramanujan's constant, 262537412640768743.99999999999925...
    assert_eq!(
        approx("approx(exp(pi*sqrt(163)), 40)"),
        "2.625374126407687439999999999992500725972e17"
    );
    assert_eq!(approx("approx(sqrt(2)+sqrt(3)-sqrt(5+2*sqrt(6)))"), "0.0");
    assert_eq!(approx("approx(exp(1)-e)"), "0.0");
}

#[test]
fn approx_numerical_integrals() {
    assert_eq!(
        approx("approx(integrate(exp(-x^2), x, 0, 1))"),
        "0.746824132812427"
    );
    assert_eq!(
        approx("approx(integrate(sin(x)/x, x, 0, 1))"),
        "0.946083070367183"
    );
    assert_eq!(approx("approx(integrate(1/sqrt(x), x, 0, 1))"), "2.0");
    // pi^4/15
    assert_eq!(
        approx("approx(integrate(x^3/(exp(x)-1), x, 0, oo))"),
        "6.49393940226683"
    );
}

#[test]
#[ignore = "future: numerical integration of oscillating integrands on infinite intervals"]
fn approx_oscillating_integrals() {
    assert_eq!(
        approx("approx(integrate(sin(x)/x, x, 0, oo))"),
        "1.5707963267949"
    );
}

#[test]
fn approx_gamma_function_family() {
    assert_eq!(approx("approx(euler_gamma)"), "0.577215664901533");
    assert_eq!(
        approx("approx(euler_gamma, 40)"),
        "0.5772156649015328606065120900824024310422"
    );
    assert_eq!(approx("approx(gamma(1/3))"), "2.67893853470775");
    assert_eq!(approx("approx(gamma(-3/2))"), "2.36327180120735");
    assert_eq!(approx("approx(factorial(1/2))"), "0.886226925452758");
    assert_eq!(approx("approx(zeta(3))"), "1.20205690315959");
    assert_eq!(approx("approx(zeta(3/2))"), "2.61237534868549");
    assert_eq!(approx("approx(digamma(1/3))"), "-3.13203378002081");
    assert_eq!(approx("approx(polygamma(1, 1/4))"), "17.1973291545071");
    assert_eq!(approx("approx(binomial(1/3, 1/2))"), "0.892656852710187");
}

#[test]
fn approx_keeps_singular_values() {
    assert_eq!(approx("approx(ln(0))"), "ln(0.0)");
    assert_eq!(approx("approx(gamma(-1))"), "gamma(-1.0)");
    assert_eq!(approx("approx(zeta(1))"), "zeta(1.0)");
    assert_eq!(approx("approx(digamma(0))"), "polygamma(0, 0.0)");
    // Evaluated exactly before being approximated
    assert_eq!(approx("approx(binomial(1/2, 2))"), "-0.125");
}

#[test]
fn tiny_intermediate_values_keep_their_precision() {
    // `{$e^(-90)$}` used to be evaluated in fixed point, losing its relative precision
    assert_eq!(
        approx("approx(ln(2*exp(-90)), 25)"),
        "-89.30685281944005469058277"
    );
    // `{$W_(-1)$}` of tiny arguments depends on their relative precision
    assert_eq!(
        approx("approx(lambertw(-2*exp(-90), -1), 25)"),
        "-93.84853497203679093594952"
    );
    assert_eq!(approx("approx(exp(-2000))"), "2.57653587296115e-869");
}

#[test]
fn approx_rootof() {
    assert_eq!(approx("approx(rootof(x^5 - x - 1, 1))"), "1.16730397826142");
    assert_eq!(
        approx("approx(rootof(x^5 - x - 1, 1), 50)"),
        "1.1673039782614186842560458998548421807205603715255"
    );
    assert_eq!(
        approx("approx(rootof(x^5 - 5*x + 1, 1))"),
        "-1.54165168410452"
    );
    assert_eq!(
        approx("approx(rootof(x^5 - x - 1, 1)^2 + 1)"),
        "2.36259857766493"
    );
}
