//! Builtin functions evaluated during normalization.

use formalith::{
    context::Context,
    field::{complex::C, real::R},
    parse,
    term::Term,
    try_parse,
};

#[test]
fn expand() {
    assert_eq!(parse!("expand((x+1)^2)", R), parse!("x^2+2*x+1", R));
}

#[test]
fn factor() {
    assert_eq!(parse!("factor(x^2-1)", R), parse!("(x-1)*(x+1)", R));
    assert_eq!(parse!("factor(expand((x+1)^2))", R), parse!("(x+1)^2", R));
}

#[test]
fn simplify() {
    assert_eq!(parse!("simplify((x^2-1)/(x-1))", R), parse!("x+1", R));
}

#[test]
fn abs() {
    assert_eq!(parse!("abs(-3*x)", R), parse!("3*abs(x)", R));
    assert_eq!(parse!("abs(abs(x))", R), parse!("abs(x)", R));
    assert_eq!(parse!("abs(x)^2", R), parse!("x^2", R));
    assert_eq!(parse!("abs(x^2)", R), parse!("x^2", R));
    assert_eq!(parse!("abs(x^3)", R), parse!("abs(x)^3", R));
    assert_eq!(parse!("abs(x*y)^2", R), parse!("x^2*y^2", R));
    assert_eq!(parse!("sqrt(x^2)", R), parse!("abs(x)", R));
    assert_eq!(parse!("sqrt(x^4)", R), parse!("x^2", R));
    assert_eq!(parse!("(x^3)^(1/3)", R), parse!("x", R));
}

#[test]
fn floor_ceil_idempotent() {
    assert_eq!(parse!("floor(floor(x))", R), parse!("floor(x)", R));
    assert_eq!(parse!("ceil(floor(x))", R), parse!("floor(x)", R));
}

#[test]
fn radicals() {
    assert_eq!(parse!("sqrt(8)", R), parse!("2*2^(1/2)", R));
    assert_eq!(parse!("16^(1/3)", R), parse!("2*2^(1/3)", R));
    assert_eq!(parse!("sqrt(2)*sqrt(3)", R), parse!("6^(1/2)", R));
    assert_eq!(parse!("sqrt(18)/sqrt(2)", R), 3.into());
    assert_eq!(parse!("sqrt(8)+sqrt(2)", R), parse!("3*2^(1/2)", R));
}

#[test]
fn roots() {
    assert_eq!(parse!("sqrt(4)", R), 2.into());
    assert_eq!(parse!("sqrt(4/9)", R), parse!("2/3", R));
    assert_eq!(parse!("sqrt(x)", R), parse!("x^(1/2)", R));
    assert_eq!(parse!("root(27, 3)", R), 3.into());
    assert_eq!(parse!("root(x, n)", R), parse!("x^(1/n)", R));
    assert_eq!(parse!("sqrt(-4)", C), parse!("2*i", C));
    assert_eq!(parse!("root(x, 3)", C), parse!("x^(1/3)", C));
}

#[test]
fn sign() {
    assert_eq!(parse!("sign(-3)", R), (-1).into());
    assert_eq!(parse!("sign(0)", R), 0.into());
    assert_eq!(parse!("sign(1/2)", R), 1.into());
    assert_eq!(parse!("sign(x)", R).to_string(), "sign(x)");
}

#[test]
fn rounding() {
    assert_eq!(parse!("floor(7/2)", R), 3.into());
    assert_eq!(parse!("floor(-7/2)", R), (-4).into());
    assert_eq!(parse!("ceil(7/2)", R), 4.into());
    assert_eq!(parse!("ceil(-7/2)", R), (-3).into());
    assert_eq!(parse!("floor(3)", R), 3.into());
    assert_eq!(parse!("floor(x)", R).to_string(), "floor(x)");
}

#[test]
fn extremum() {
    assert_eq!(parse!("min(3, 1, 2)", R), 1.into());
    assert_eq!(parse!("max(3, 1, 2)", R), 3.into());
    assert_eq!(parse!("max(x)", R), parse!("x", R));
    assert_eq!(parse!("max(3, x, 1, x)", R), parse!("max(x, 3)", R));
    assert_eq!(parse!("min(x, y)", R).to_string(), "min(x, y)");
}

#[test]
fn gcd_lcm() {
    assert_eq!(parse!("gcd(12, 18)", R), 6.into());
    assert_eq!(parse!("lcm(4, 6)", R), 12.into());
    assert_eq!(parse!("gcd(0, 5)", R), 5.into());
    assert_eq!(parse!("gcd(1/2, 3/4)", R), parse!("1/4", R));
    assert_eq!(parse!("lcm(1/2, 3/4)", R), parse!("3/2", R));
    assert_eq!(parse!("gcd(x^2-1, x^2+2*x+1)", R), parse!("x+1", R));
    assert_eq!(parse!("lcm(x^2-1, x+1)", R), parse!("x^2-1", R));
    assert_eq!(parse!("gcd(x, 0)", R), parse!("x", R));
    assert_eq!(parse!("lcm(x, 0)", R), 0.into());
}

#[test]
fn wrong_arity() {
    assert!(try_parse!("expand(x, y)", R).is_err());
    assert!(try_parse!("factor()", R).is_err());
    assert!(try_parse!("sqrt(x, y)", R).is_err());
    assert!(try_parse!("root(x)", R).is_err());
    assert!(try_parse!("gcd(x, y, z)", R).is_err());
    assert!(try_parse!("min(x, y, z)", R).is_ok());
}

#[test]
fn diff() {
    assert_eq!(parse!("diff(x^3, x)", R), parse!("3*x^2", R));
    assert_eq!(parse!("diff(y, x)", R), parse!("0", R));
    assert_eq!(parse!("diff(5, x)", R), parse!("0", R));
    assert_eq!(parse!("diff(x*y + x^2, x)", R), parse!("y + 2*x", R));
    assert_eq!(parse!("diff((x+1)^2, x)", R), parse!("2*(x+1)", R));
    assert_eq!(parse!("diff(3*x*y*x, x)", R), parse!("6*x*y", R));
    assert_eq!(parse!("diff(sqrt(x), x)", R), parse!("1/2*x^(-1/2)", R));
    assert_eq!(parse!("diff(1/x, x)", R), parse!("-x^(-2)", R));
    assert_eq!(parse!("diff(diff(x^3, x), x)", R), parse!("6*x", R));
    assert_eq!(parse!("diff(i*x^2, x)", C), parse!("2*i*x", C));
}

#[test]
fn diff_unevaluated() {
    let is_diff = |term| matches!(term, Term::Fun(fun) if fun.get_ident() == Context::DIFF);
    assert!(is_diff(parse!("diff(x^x, x)", R)));
    assert_eq!(
        parse!("diff(f(x) + x^2, x)", R),
        parse!("diff(f(x), x) + 2*x", R)
    );
    assert!(is_diff(parse!("diff(x, 2)", R)));
}

#[test]
fn reciprocal_trigonometric_functions() {
    assert_eq!(parse!("sec(x)", R), parse!("1/cos(x)", R));
    assert_eq!(parse!("csc(x)", R), parse!("1/sin(x)", R));
    assert_eq!(parse!("cot(x)", R), parse!("cos(x)/sin(x)", R));
}

#[test]
fn logarithm_in_base() {
    assert_eq!(parse!("log(8, 2)", R), parse!("3", R));
    assert_eq!(parse!("log(1/9, 3)", R), parse!("-2", R));
    assert_eq!(parse!("log(4, 1/2)", R), parse!("-2", R));
    assert_eq!(parse!("log(1000)", R), parse!("3", R));
    assert_eq!(parse!("log(1/100)", R), parse!("-2", R));
    assert_eq!(parse!("log(x)", R), parse!("ln(x)/ln(10)", R));
    assert_eq!(parse!("log(6, 2)", R), parse!("ln(6)/ln(2)", R));
}

#[test]
fn inverse_trigonometric_values() {
    assert_eq!(parse!("asin(1/2)", R), parse!("pi/6", R));
    assert_eq!(parse!("asin(-sqrt(2)/2)", R), parse!("-pi/4", R));
    assert_eq!(parse!("asin(1)", R), parse!("pi/2", R));
    assert_eq!(parse!("acos(-1)", R), parse!("pi", R));
    assert_eq!(parse!("acos(sqrt(3)/2)", R), parse!("pi/6", R));
    assert_eq!(parse!("acos(0)", R), parse!("pi/2", R));
    assert_eq!(parse!("atan(sqrt(3))", R), parse!("pi/3", R));
    assert_eq!(parse!("atan(-1)", R), parse!("-pi/4", R));
    assert_eq!(parse!("atan(sqrt(3)/3)", R), parse!("pi/6", R));
    assert!(matches!(parse!("asin(1/3)", R), Term::Fun(_)));
}

#[test]
fn hyperbolic_values() {
    assert_eq!(parse!("sinh(0)", R), parse!("0", R));
    assert_eq!(parse!("cosh(0)", R), parse!("1", R));
    assert_eq!(parse!("tanh(0)", R), parse!("0", R));
    assert_eq!(parse!("asinh(0)", R), parse!("0", R));
    assert_eq!(parse!("acosh(1)", R), parse!("0", R));
    assert_eq!(parse!("atanh(0)", R), parse!("0", R));
}

#[test]
fn factorial_and_binomial() {
    assert_eq!(parse!("factorial(0)", R), parse!("1", R));
    assert_eq!(parse!("factorial(5)", R), parse!("120", R));
    assert_eq!(parse!("binomial(5, 2)", R), parse!("10", R));
    assert_eq!(parse!("binomial(2, 5)", R), parse!("0", R));
    assert_eq!(parse!("binomial(5, -1)", R), parse!("0", R));
    assert!(matches!(parse!("factorial(x)", R), Term::Fun(_)));
    assert!(matches!(parse!("factorial(-1)", R), Term::Fun(_)));
    assert!(matches!(parse!("factorial(1/2)", R), Term::Fun(_)));
}

#[test]
fn derivatives_of_classic_functions() {
    assert_eq!(parse!("diff(atan(x), x)", R), parse!("1/(1+x^2)", R));
    assert_eq!(parse!("diff(asin(x), x)", R), parse!("(1-x^2)^(-1/2)", R));
    assert_eq!(parse!("diff(acos(x), x)", R), parse!("-(1-x^2)^(-1/2)", R));
    assert_eq!(parse!("diff(sinh(x), x)", R), parse!("cosh(x)", R));
    assert_eq!(parse!("diff(cosh(x), x)", R), parse!("sinh(x)", R));
    assert_eq!(parse!("diff(tanh(x), x)", R), parse!("1-tanh(x)^2", R));
    assert_eq!(parse!("diff(asinh(x), x)", R), parse!("(x^2+1)^(-1/2)", R));
    assert_eq!(parse!("diff(acosh(x), x)", R), parse!("(x^2-1)^(-1/2)", R));
    assert_eq!(parse!("diff(atanh(x), x)", R), parse!("1/(1-x^2)", R));
    assert_eq!(parse!("diff(atan(2*x), x)", R), parse!("2/(1+4*x^2)", R));
    assert_eq!(parse!("diff(log(x), x)", R), parse!("1/(x*ln(10))", R));
}

#[test]
fn exponential_powers() {
    assert_eq!(parse!("exp(x)*exp(x)", R), parse!("exp(2*x)", R));
    assert_eq!(parse!("1/exp(x)", R), parse!("exp(-x)", R));
}

#[test]
fn constant_radicals() {
    assert_eq!(parse!("sqrt(2*pi)/(sqrt(2)*sqrt(pi))", R), parse!("1", R));
    assert_eq!(parse!("sqrt(2)*sqrt(2)*y", R), parse!("2*y", R));
}

#[test]
fn trigonometric_values_at_classic_angles() {
    assert_eq!(parse!("sin(pi)", R), parse!("0", R));
    assert_eq!(parse!("sin(100*pi)", R), parse!("0", R));
    assert_eq!(parse!("cos(3*pi/2)", R), parse!("0", R));
    assert_eq!(parse!("cos(5*pi/6)", R), parse!("-sqrt(3)/2", R));
    assert_eq!(parse!("sin(7*pi/4)", R), parse!("-sqrt(2)/2", R));
    assert_eq!(parse!("tan(pi/3)", R), parse!("sqrt(3)", R));
    assert_eq!(parse!("tan(pi/4)", R), parse!("1", R));
    assert_eq!(parse!("cos(-pi)", R), parse!("-1", R));
}

#[test]
fn tangent_at_its_poles_stays_unevaluated() {
    assert!(matches!(parse!("tan(pi/2)", R), Term::Fun(_)));
}

#[test]
#[ignore = "future: exact values at pi/12, pi/5 and other angles with radicals"]
fn trigonometric_values_with_radicals() {
    assert_eq!(parse!("sin(pi/12)", R), parse!("(sqrt(6)-sqrt(2))/4", R));
    assert_eq!(parse!("cos(pi/5)", R), parse!("(1+sqrt(5))/4", R));
    assert_eq!(parse!("cos(pi/8)", R), parse!("sqrt(2+sqrt(2))/2", R));
}

#[test]
#[ignore = "future: parity and periodicity of trigonometric functions"]
fn trigonometric_symmetries() {
    assert_eq!(parse!("sin(-x)", R), parse!("-sin(x)", R));
    assert_eq!(parse!("cos(-x)", R), parse!("cos(x)", R));
    assert_eq!(parse!("cos(x+2*pi)", R), parse!("cos(x)", R));
    assert_eq!(parse!("sin(x+pi)", R), parse!("-sin(x)", R));
    assert_eq!(parse!("tan(x+pi)", R), parse!("tan(x)", R));
}

#[test]
fn exponentials_and_logarithms() {
    assert_eq!(parse!("ln(1)", R), parse!("0", R));
    assert_eq!(parse!("ln(e)", R), parse!("1", R));
    assert_eq!(parse!("ln(e^3)", R), parse!("3", R));
    assert_eq!(parse!("ln(exp(x))", R), parse!("x", R));
    assert_eq!(parse!("exp(0)", R), parse!("1", R));
    assert_eq!(parse!("e^(ln(2))", R), parse!("2", R));
    assert_eq!(parse!("log(1000)", R), parse!("3", R));
    assert_eq!(parse!("log(8, 2)", R), parse!("3", R));
    // ln(x) is only defined for x > 0, so exp(ln(x)) = x, but ln(0) stays unevaluated
    assert!(matches!(parse!("ln(0)", R), Term::Fun(_)));
}

#[test]
fn inverse_functions_out_of_their_domain() {
    assert!(matches!(parse!("asin(2)", R), Term::Fun(_)));
    assert!(matches!(parse!("acos(-3/2)", R), Term::Fun(_)));
    assert_eq!(parse!("atan(-sqrt(3))", R), parse!("-pi/3", R));
    assert_eq!(parse!("erf(0)", R), parse!("0", R));
}

#[test]
#[ignore = "future: values of functions at infinity"]
fn functions_at_infinity() {
    assert_eq!(parse!("atan(oo)", R), parse!("pi/2", R));
    assert_eq!(parse!("exp(-oo)", R), parse!("0", R));
    assert_eq!(parse!("tanh(oo)", R), parse!("1", R));
}

#[test]
fn big_factorials_and_binomials() {
    assert_eq!(parse!("factorial(20)", R), parse!("2432902008176640000", R));
    assert_eq!(parse!("binomial(50, 25)", R), parse!("126410606437752", R));
    assert_eq!(parse!("binomial(5, 0)", R), parse!("1", R));
    assert_eq!(parse!("binomial(5, 5)", R), parse!("1", R));
    assert_eq!(parse!("binomial(5, 6)", R), parse!("0", R));
    assert_eq!(parse!("factorial(30)/factorial(28)", R), parse!("870", R));
    assert_eq!(
        parse!("factorial(100)", R),
        parse!(
            "93326215443944152681699238856266700490715968264381621468592963895217599993229915608941463976156518286253697920827223758251185210916864000000000000000000000000",
            R
        )
    );
}

#[test]
#[ignore = "future: symbolic and generalized binomials and factorials"]
fn generalized_factorials_and_binomials() {
    assert_eq!(parse!("binomial(n, 0)", R), parse!("1", R));
    assert_eq!(parse!("binomial(n, 1)", R), parse!("n", R));
    assert_eq!(parse!("binomial(-1, 3)", R), parse!("-1", R));
    assert_eq!(parse!("binomial(1/2, 2)", R), parse!("-1/8", R));
    assert_eq!(parse!("factorial(1/2)", R), parse!("sqrt(pi)/2", R));
}

#[test]
fn derivatives_of_compositions() {
    assert_eq!(parse!("diff(abs(x), x)", R), parse!("sign(x)", R));
    assert_eq!(parse!("diff(sign(x), x)", R), parse!("0", R));
    assert_eq!(parse!("diff(x^n, x)", R), parse!("n*x^(n-1)", R));
    assert_eq!(parse!("diff(exp(exp(x)), x)", R), parse!("exp(x+exp(x))", R));
    assert_eq!(
        parse!("diff(sin(x)*cos(x), x)", R),
        parse!("cos(x)^2-sin(x)^2", R)
    );
    assert_eq!(
        parse!("diff(x/(x+1), x)", R),
        parse!("1/(x+1)-x/(x+1)^2", R)
    );
    assert_eq!(parse!("diff(sqrt(1+x^2), x)", R), parse!("x/sqrt(x^2+1)", R));
    assert_eq!(parse!("diff(ln(sin(x)), x)", R), parse!("cos(x)/sin(x)", R));
    assert_eq!(parse!("diff(log(x, 2), x)", R), parse!("1/(x*ln(2))", R));
    assert_eq!(parse!("diff(x^(1/3), x)", R), parse!("1/3*x^(-2/3)", R));
    assert_eq!(
        parse!("diff(erf(x), x)", R),
        parse!("2/sqrt(pi)*exp(-x^2)", R)
    );
    assert_eq!(
        parse!("diff(erfi(x), x)", R),
        parse!("2/sqrt(pi)*exp(x^2)", R)
    );
    assert_eq!(parse!("diff(e^x, x)", R), parse!("exp(x)", R));
    assert_eq!(parse!("diff(x, x)", R), parse!("1", R));
    assert_eq!(parse!("diff(pi, x)", R), parse!("0", R));
    assert_eq!(parse!("diff(x^2*y^3, y)", R), parse!("3*x^2*y^2", R));
    assert_eq!(
        parse!("diff(diff(diff(diff(sin(x), x), x), x), x)", R),
        parse!("sin(x)", R)
    );
    assert_eq!(
        parse!("diff(series(sin(x), x, 0, 4), x)", R),
        parse!("1-x^2/2", R)
    );
}

#[test]
#[ignore = "future: derivatives of powers with a variable exponent"]
fn derivatives_of_variable_powers() {
    assert_eq!(parse!("diff(x^x, x)", R), parse!("x^x*(ln(x)+1)", R));
    assert_eq!(parse!("diff(a^x, x)", R), parse!("a^x*ln(a)", R));
    assert_eq!(parse!("diff(2^x, x)", R), parse!("2^x*ln(2)", R));
}

#[test]
#[ignore = "future: fundamental theorem of calculus, d/dx integrate(f(t), t, a, x) = f(x)"]
fn derivative_of_an_integral_with_a_variable_bound() {
    assert_eq!(
        parse!("diff(integrate(exp(-t^2)*ln(t), t, 1, x), x)", R),
        parse!("exp(-x^2)*ln(x)", R)
    );
}

#[test]
fn derivatives_of_unknown_functions_stay_unevaluated() {
    assert!(matches!(parse!("diff(f(x), x)", R), Term::Fun(_)));
    assert!(matches!(parse!("diff(floor(x), x)", R), Term::Fun(_)));
    assert!(matches!(parse!("diff(factorial(x), x)", R), Term::Fun(_)));
}
