//! Integrals with `integrate`: antiderivatives, definite and improper integrals, numerical approximations.
use formalith::{
    context::Context,
    field::real::R,
    parse, symbol,
    term::{Fun, Normalize, Term},
};

mod common;
use common::line;

fn integrate(input: &str) -> String {
    line(&parse!(input, R))
}

/// Check that `integrate(f, x)` is evaluated, and that its derivative is `f` at a few points.
fn check(f: &str) {
    let x = symbol!("x");
    let integral = parse!(&format!("integrate({f}, x)"), R);
    let printed = line(&integral);
    assert!(!printed.contains("integrate"), "{f} not integrated: {printed}");
    let difference = integral.derivative(x) - parse!(f, R);
    for point in ["3/10", "7/10", "13/10", "21/10"] {
        let at = difference.substitute(x, &parse!(point, R)).unwrap();
        // Shifted by 1, as approximating an exact 0 raises the precision until its maximum
        let shifted = at + Term::one(R);
        let approximated =
            line(&Term::Fun(Box::new(Fun::new(Context::APPROX, vec![shifted], R))).normalize());
        let value: f64 = approximated
            .parse::<f64>()
            .unwrap_or_else(|_| panic!("{f}: {printed}, derivative at {point}: {approximated}"))
            - 1.;
        assert!(value.abs() < 1e-10, "{f}: {printed}, derivative error at {point}: {value}");
    }
}

#[test]
fn rational_functions() {
    assert_eq!(integrate("integrate(x^2, x)"), "1/3*(x^3)");
    assert_eq!(integrate("integrate(1/(x^2+1), x)"), "atan(x)");
    for f in [
        "1/x",
        "1/(x^3-1)",
        "(x^2+1)/(x^2-1)^2",
        "1/(x^4+1)",
        "1/(x^2-2)",
        "x/(x^2+x+1)",
        "1/(x^3-2)",
        "1/(x^4-2)",
        "(x^5+3*x)/(x^2+1)^3",
        "1/(x*(x+1)^2)",
        "1/(x^6+1)",
    ] {
        check(f);
    }
}

#[test]
fn parameters() {
    assert_eq!(integrate("integrate(2^x, x)"), integrate("2^x/ln(2)"));
    assert_eq!(integrate("integrate(a*x^n, x)"), integrate("a*x^(n+1)/(n+1)"));
    assert_eq!(integrate("integrate(exp(a*x), x)"), integrate("exp(a*x)/a"));
    assert_eq!(integrate("integrate(1/(x+a), x)"), integrate("ln(abs(x+a))"));
}

#[test]
fn elementary_functions() {
    for f in [
        "cos(x)", "sin(2*x+1)", "exp(3*x)", "tan(x)", "sinh(x)", "cosh(2*x)", "tanh(x)", "ln(x)",
        "asin(x/3)", "acos(x/3)", "atan(x)", "asinh(x)", "acosh(x+1)", "atanh(x/3)", "sqrt(x)", "(2*x+1)^(3/2)",
        "1/sqrt(1-x^2/9)", "1/sqrt(x^2+1)", "1/sqrt(x^2-1/20)", "sqrt(9-x^2)", "sqrt(x^2+x+1)", "(x^2+1)^(-3/2)",
        "x/sqrt(x^2+x+1)", "exp(x)*sin(2*x)", "exp(-x)*cos(x)", "abs(x)",
    ] {
        check(f);
    }
}

#[test]
fn trigonometric_powers() {
    for f in [
        "sin(x)^2", "sin(x)^3*cos(x)^2", "cos(x)^4", "sin(x)^2*cos(x)^2", "1/cos(x)^2", "tan(x)^2", "tan(x)^3",
        "1/sin(x)", "sin(x)/cos(x)^3", "sin(x)*cos(x)", "sin(2*x)*cos(3*x)", "sin(x)*sin(3*x)",
        "1/(2+cos(x))", "1/(1+sin(x)+cos(x))",
    ] {
        check(f);
    }
}

#[test]
fn substitutions_and_parts() {
    for f in [
        "x*exp(x^2)", "2*x*cos(x^2)", "ln(x)/x", "exp(x)/(1+exp(x))", "1/(1+exp(x))", "exp(2*x)/(exp(x)+1)",
        "x*sqrt(x+1)", "sin(x)*exp(cos(x))", "1/(x*ln(x))", "cos(sqrt(x))/sqrt(x)", "x/(2*x+3)^(1/2)",
        "x*exp(x)", "x^2*sin(x)", "x*ln(x)", "ln(x)^2", "x*atan(x)", "x^2*exp(x)*cos(x)", "1/cosh(x)",
        "sinh(x)^2", "exp(x)*sinh(x)", "atan(x)/(1+x^2)", "sqrt(1+sqrt(x))",
    ] {
        check(f);
    }
}

#[test]
fn definite_integrals() {
    assert_eq!(integrate("integrate(x^2, x, 0, 1)"), "1/3");
    assert_eq!(integrate("integrate(x, x, 0, a)"), "1/2*(a^2)");
    assert_eq!(integrate("integrate(1/x^2, x, 1, oo)"), "1");
    assert_eq!(integrate("integrate(exp(-x), x, 0, oo)"), "1");
    assert_eq!(integrate("integrate(1/(x^2+1), x, -oo, oo)"), "pi");
    assert_eq!(integrate("integrate(1/sqrt(x), x, 0, 1)"), "2");
    assert_eq!(integrate("integrate(ln(x), x, 0, 1)"), "-1");
    assert_eq!(integrate("integrate(sin(x), x, 0, pi)"), "2");
    assert_eq!(integrate("integrate(x^2, x, 1, 0)"), "-1/3");
    assert_eq!(integrate("integrate(1/x, x, -1, 1)"), "undefined");
    assert_eq!(integrate("integrate(1/x^2, x, -1, 1)"), "oo");
    assert_eq!(integrate("integrate(1/x, x, 1, oo)"), "oo");
    assert_eq!(integrate("integrate(sin(x), x, 0, oo)"), "undefined");
    assert_eq!(integrate("integrate(1/(2+cos(x)), x, 0, 2*pi)"), integrate("2*pi*sqrt(3)/3"));
    assert_eq!(integrate("integrate(tan(x)^2, x, 0, 1)"), integrate("tan(1) - 1"));
    assert_eq!(integrate("integrate(x*exp(-x^2), x, -oo, oo)"), "0");
}

#[test]
fn numerical_integrals() {
    assert_eq!(integrate("approx(integrate(exp(-x^2), x, 0, 1))"), "0.746824132812427");
    assert_eq!(integrate("approx(integrate(exp(-x^2), x, -oo, oo))"), "1.77245385090552");
    assert_eq!(integrate("approx(integrate(exp(-x)*ln(x), x, 0, oo))"), "-0.577215664901533");
    assert_eq!(integrate("approx(integrate(exp(-x^2), x, 1, 0))"), "-0.746824132812427");
    assert_eq!(integrate("approx(integrate(x^x, x, 0, 1))"), "0.783430510712134");
    assert_eq!(integrate("approx(integrate(exp(-x)/sqrt(x), x, 0, 1))"), "1.49364826562485");
    // Slowly decaying oscillations don't converge, the integral stays unevaluated
    assert!(integrate("approx(integrate(sin(x)/x, x, 0, oo))").contains("integrate"));
}
