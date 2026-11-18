//! Series expansions with `series`, computed with the series of the Gruntz algorithm.
use formalith::{field::real::R, parse};

mod common;
use common::line;

fn series(input: &str) -> String {
    line(&parse!(input, R))
}

#[test]
fn taylor_series_at_zero() {
    assert_eq!(series("series(exp(x), x, 0, 4)"), "x+1/2*(x^2)+1/6*(x^3)+1");
    assert_eq!(series("series(sin(x), x, 0)"), "x-1/6*(x^3)+1/120*(x^5)");
    assert_eq!(series("series(cos(x), x, 0)"), "-1/2*(x^2)+1/24*(x^4)+1");
    assert_eq!(series("series(tan(x), x, 0, 8)"), "x+1/3*(x^3)+2/15*(x^5)+17/315*(x^7)");
    assert_eq!(series("series(ln(1+x), x, 0)"), "x-1/2*(x^2)+1/3*(x^3)-1/4*(x^4)+1/5*(x^5)");
    assert_eq!(series("series(1/(1-x), x, 0, 4)"), "x+x^2+x^3+1");
    assert_eq!(series("series(sqrt(1+x), x, 0, 3)"), "1/2*x-1/8*(x^2)+1");
    assert_eq!(series("series(exp(sin(x)), x, 0, 5)"), "x+1/2*(x^2)-1/8*(x^4)+1");
    assert_eq!(series("series(sin(x)/x, x, 0, 6)"), "-1/6*(x^2)+1/120*(x^4)+1");
}

#[test]
fn polynomials_are_truncated() {
    assert_eq!(series("series(x^3+2*x, x, 0, 2)"), "2*x");
    assert_eq!(series("series(x^3+2*x, x, 0)"), "2*x+x^3");
}

#[test]
fn series_at_a_point() {
    assert_eq!(series("series(exp(x), x, 1, 3)"), "exp(1)+(x-1)*exp(1)+1/2*((x-1)^2)*exp(1)");
    assert_eq!(series("series(ln(x), x, 1, 4)"), "x-1/2*((x-1)^2)+1/3*((x-1)^3)-1");
    assert_eq!(series("series(1/x, x, a, 3)"), "a^-1-(x-a)*(a^-2)+((x-a)^2)*(a^-3)");
    assert_eq!(series("series(exp(a*x), x, 0, 3)"), "x*a+1/2*(x^2)*(a^2)+1");
}

#[test]
fn laurent_and_puiseux_series() {
    assert_eq!(series("series(1/sin(x), x, 0, 4)"), "1/6*x+x^-1+7/360*(x^3)");
    assert_eq!(series("series(cos(x)/x^2, x, 0, 3)"), "x^-2+1/24*(x^2)-1/2");
    assert_eq!(series("series(1/(x^2-1), x, 1, 1)"), "1/2*((x-1)^-1)-1/4");
    assert_eq!(series("series(1/x, x, 0)"), "x^-1");
    assert_eq!(series("series(sqrt(x), x, 0, 2, 1)"), "x^1/2");
    assert_eq!(series("series(x^x, x, 0, 3, 1)"), "x*ln(x)+1/2*(x^2)*(ln(x)^2)+1");
    assert_eq!(series("series(abs(x), x, 0, 3, -1)"), "-x");
}

#[test]
fn series_at_infinity() {
    assert_eq!(series("series(1/(1-x), x, oo, 3)"), "-(x^-2)-(x^-1)");
    assert_eq!(series("series(sqrt(x^2+1)-x, x, oo, 4)"), "-1/8*(x^-3)+1/2*(x^-1)");
    assert_eq!(series("series(x, x, -oo, 3)"), "x");
}

#[test]
fn unsupported_series_stay_unevaluated() {
    // Both sides differ, or the left side isn't real
    assert_eq!(series("series(abs(x), x, 0)"), "series(abs(x), x, 0)");
    assert_eq!(series("series(sqrt(x), x, 0, 2)"), "series(x^1/2, x, 0, 2)");
    // Not a power series
    assert_eq!(series("series(exp(x), x, oo)"), "series(exp(x), x, oo)");
    assert_eq!(series("series(exp(1/x), x, 0)"), "series(exp(x^-1), x, 0)");
    assert_eq!(series("series(floor(x), x, 0)"), "series(floor(x), x, 0)");
    assert_eq!(series("series(x^2, x+1, 0)"), "series(x^2, x+1, 0)");
}

#[test]
fn roots_of_negative_values_are_unsupported() {
    assert_eq!(series("lim(sqrt(x), x, 0, -1)"), "lim(x^1/2, x, 0, -1)");
}

#[test]
fn series_of_classic_functions() {
    let eq = |a: &str, b: &str| assert_eq!(parse!(a, R), parse!(b, R), "{a}");
    eq("series(atan(x), x, 0, 6)", "x - x^3/3 + x^5/5");
    eq("series(asin(x), x, 0, 4)", "x + x^3/6");
    eq("series(acos(x), x, 0, 4)", "pi/2 - x - x^3/6");
    eq("series(sinh(x), x, 0, 4)", "x + x^3/6");
    eq("series(cosh(x), x, 0, 4)", "1 + x^2/2");
    eq("series(tanh(x), x, 0, 4)", "x - x^3/3");
    eq("series(atanh(x), x, 0, 4)", "x + x^3/3");
    eq("series(asinh(x), x, 0, 4)", "x - x^3/6");
    eq("series(atan(x), x, 1, 3)", "pi/4 + (x-1)/2 - (x-1)^2/4");
    eq("series(atan(x), x, oo, 4)", "pi/2 - 1/x + 1/(3*x^3)");
}
