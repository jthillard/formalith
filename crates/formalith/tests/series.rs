//! Series expansions with `series`, computed with the series of the Gruntz algorithm.
use formalith::{field::real::R, parse};

mod common;
use common::{line, split_remainder};

/// The terms of a series, without its remainder.
fn series(input: &str) -> String {
    let printed = line(&parse!(input, R));
    match split_remainder(&printed) {
        (terms, Some(_)) => terms,
        (_, None) => printed,
    }
}

#[test]
fn remainders() {
    let remainder = |input: &str| split_remainder(&line(&parse!(input, R))).1;
    assert_eq!(remainder("series(exp(x), x, 0, 4)").as_deref(), Some("x^3"));
    assert_eq!(remainder("series(sin(x), x, 0)").as_deref(), Some("x^5"));
    assert_eq!(
        remainder("series(ln(x), x, 1, 3)").as_deref(),
        Some("(x-1)^2")
    );
    assert_eq!(remainder("series(1/x, x, oo, 3)").as_deref(), Some("x^-2"));
    assert_eq!(remainder("series(1/sin(x), x, 0, 2)").as_deref(), Some("x"));
    assert_eq!(
        remainder("series(sqrt(x), x, 0, 2, 1)").as_deref(),
        Some("x")
    );
    assert_eq!(line(&parse!("series(x^3, x, 0, 2)", R)), "o(x)");
    assert_eq!(line(&parse!("series(exp(x), x, 0, 1)", R)), "1+o(1)");
    // Unevaluated series have none
    assert_eq!(remainder("series(exp(1/x), x, 0)"), None);
}

#[test]
fn little_o_absorbs_factors() {
    assert_eq!(line(&parse!("3*o(x^2)", R)), "o(x^2)");
    assert_eq!(line(&parse!("-o(x^2)", R)), "o(x^2)");
    assert_eq!(line(&parse!("x*o(x^2)", R)), "o(x^3)");
    assert_eq!(line(&parse!("o(x)*o(x^2)", R)), "o(x^3)");
    assert_eq!(line(&parse!("o(-2*x)", R)), "o(x)");
    assert_eq!(line(&parse!("o(x) - o(x)", R)), "o(x)");
    assert_eq!(
        line(&parse!("expand(2*series(exp(x), x, 0, 2))", R)),
        "2*x+2+o(x)"
    );
}

#[test]
fn taylor_series_at_zero() {
    assert_eq!(series("series(exp(x), x, 0, 4)"), "x+1/2*(x^2)+1/6*(x^3)+1");
    assert_eq!(series("series(sin(x), x, 0)"), "x-1/6*(x^3)+1/120*(x^5)");
    assert_eq!(series("series(cos(x), x, 0)"), "-1/2*(x^2)+1/24*(x^4)+1");
    assert_eq!(
        series("series(tan(x), x, 0, 8)"),
        "x+1/3*(x^3)+2/15*(x^5)+17/315*(x^7)"
    );
    assert_eq!(
        series("series(ln(1+x), x, 0)"),
        "x-1/2*(x^2)+1/3*(x^3)-1/4*(x^4)+1/5*(x^5)"
    );
    assert_eq!(series("series(1/(1-x), x, 0, 4)"), "x+x^2+x^3+1");
    assert_eq!(series("series(sqrt(1+x), x, 0, 3)"), "1/2*x-1/8*(x^2)+1");
    assert_eq!(
        series("series(exp(sin(x)), x, 0, 5)"),
        "x+1/2*(x^2)-1/8*(x^4)+1"
    );
    assert_eq!(
        series("series(sin(x)/x, x, 0, 6)"),
        "-1/6*(x^2)+1/120*(x^4)+1"
    );
}

#[test]
fn polynomials_are_truncated() {
    assert_eq!(series("series(x^3+2*x, x, 0, 2)"), "2*x");
    assert_eq!(series("series(x^3+2*x, x, 0)"), "2*x+x^3");
}

#[test]
fn series_at_a_point() {
    assert_eq!(
        series("series(exp(x), x, 1, 3)"),
        "exp(1)+(x-1)*exp(1)+1/2*((x-1)^2)*exp(1)"
    );
    assert_eq!(
        series("series(ln(x), x, 1, 4)"),
        "x-1/2*((x-1)^2)+1/3*((x-1)^3)-1"
    );
    assert_eq!(
        series("series(1/x, x, a, 3)"),
        "a^-1-(x-a)*(a^-2)+((x-a)^2)*(a^-3)"
    );
    assert_eq!(series("series(exp(a*x), x, 0, 3)"), "x*a+1/2*(x^2)*(a^2)+1");
}

#[test]
fn laurent_and_puiseux_series() {
    assert_eq!(
        series("series(1/sin(x), x, 0, 4)"),
        "1/6*x+x^-1+7/360*(x^3)"
    );
    assert_eq!(series("series(cos(x)/x^2, x, 0, 3)"), "x^-2+1/24*(x^2)-1/2");
    assert_eq!(series("series(1/(x^2-1), x, 1, 1)"), "1/2*((x-1)^-1)-1/4");
    assert_eq!(series("series(1/x, x, 0)"), "x^-1");
    assert_eq!(series("series(sqrt(x), x, 0, 2, 1)"), "x^(1/2)");
    assert_eq!(
        series("series(x^x, x, 0, 3, 1)"),
        "x*ln(x)+1/2*(x^2)*(ln(x)^2)+1"
    );
    assert_eq!(series("series(abs(x), x, 0, 3, -1)"), "-x");
}

#[test]
fn series_at_infinity() {
    assert_eq!(series("series(1/(1-x), x, oo, 3)"), "-(x^-2)-(x^-1)");
    assert_eq!(
        series("series(sqrt(x^2+1)-x, x, oo, 4)"),
        "-1/8*(x^-3)+1/2*(x^-1)"
    );
    assert_eq!(series("series(x, x, -oo, 3)"), "x");
}

#[test]
fn unsupported_series_stay_unevaluated() {
    // Both sides differ, or the left side isn't real
    assert_eq!(series("series(abs(x), x, 0)"), "series(abs(x), x, 0)");
    assert_eq!(
        series("series(sqrt(x), x, 0, 2)"),
        "series(x^(1/2), x, 0, 2)"
    );
    // Not a power series
    assert_eq!(series("series(exp(x), x, oo)"), "series(exp(x), x, oo)");
    assert_eq!(series("series(exp(1/x), x, 0)"), "series(exp(x^-1), x, 0)");
    assert_eq!(series("series(floor(x), x, 0)"), "series(floor(x), x, 0)");
    assert_eq!(series("series(x^2, x+1, 0)"), "series(x^2, x+1, 0)");
    // Not continuous, a negative base is only real at some rational exponents
    assert_eq!(series("series((-1)^x, x, 0)"), "series((-1)^x, x, 0)");
}

#[test]
fn roots_of_negative_values_are_unsupported() {
    assert_eq!(series("lim(sqrt(x), x, 0, -1)"), "lim(x^(1/2), x, 0, -1)");
}

#[test]
fn series_of_classic_functions() {
    let eq = |a: &str, b: &str| assert_eq!(series(a), line(&parse!(b, R)), "{a}");
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

#[test]
fn series_order_edge_cases() {
    assert_eq!(series("series(ln(1+x), x, 0, 1)"), "0");
    assert_eq!(series("series(ln(1+x), x, 0, 0)"), "0");
    assert_eq!(series("series(x^10, x, 0, 3)"), "0");
    assert_eq!(series("series(1, x, 0, 3)"), "1");
    assert_eq!(series("series(y, x, 0, 3)"), "y");
    assert_eq!(series("series(cos(x)^2+sin(x)^2, x, 0, 6)"), "1");
}

#[test]
fn series_of_compositions() {
    let eq = |a: &str, b: &str| assert_eq!(series(a), line(&parse!(b, R)), "{a}");
    eq(
        "series(exp(x)/(1-x), x, 0, 4)",
        "1 + 2*x + 5/2*x^2 + 8/3*x^3",
    );
    eq("series(ln(cos(x)), x, 0, 7)", "-x^2/2 - x^4/12 - x^6/45");
    eq(
        "series(x/(exp(x)-1), x, 0, 6)",
        "1 - x/2 + x^2/12 - x^4/720",
    );
    eq("series(1/(exp(x)-1), x, 0, 3)", "1/x - 1/2 + x/12");
    eq("series(ln(sin(x)/x), x, 0, 6)", "-x^2/6 - x^4/180");
    eq("series(tan(sin(x))-sin(tan(x)), x, 0, 9)", "x^7/30");
    eq("series(sqrt(1+x)-1, x, 0, 4)", "x/2 - x^2/8 + x^3/16");
    eq("series(1/(x^2*(1+x)), x, 0, 1)", "x^-2 - x^-1 + 1");
    eq(
        "series(sqrt(x+x^2), x, 0, 3, 1)",
        "x^(1/2) + x^(3/2)/2 - x^(5/2)/8",
    );
    eq("series(atan(1/x), x, 0, 4, 1)", "pi/2 - x + x^3/3");
    eq("series(sin(x), x, pi, 4)", "-(x-pi) + (x-pi)^3/6");
    eq("series(1/x, x, 1, 3)", "1 - (x-1) + (x-1)^2");
    eq("series(sqrt(x^2+1), x, oo, 4)", "x + 1/(2*x) - 1/(8*x^3)");
    eq("series(exp(x)^(1/x), x, oo, 2)", "exp(1)");
    eq(
        "series(erf(x), x, 0, 6)",
        "2/sqrt(pi)*x - 2/(3*sqrt(pi))*x^3 + 1/(5*sqrt(pi))*x^5",
    );
}

#[test]
fn series_of_logarithms_stay_logarithms() {
    assert_eq!(series("series(ln(x), x, 0, 3, 1)"), "ln(x)");
}

#[test]
fn series_of_factorial() {
    // `euler_gamma` is the Euler-Mascheroni constant
    assert_eq!(series("series(factorial(x), x, 0, 2)"), "-euler_gamma*x+1");
    assert_eq!(
        series("series(gamma(x), x, 2, 2)"),
        "(-euler_gamma+1)*(x-2)+1"
    );
    // Laurent series at a pole
    assert_eq!(series("series(gamma(x), x, 0, 1)"), "-euler_gamma+x^-1");
    assert_eq!(
        series("series(gamma(x), x, 1, 3)"),
        series("1 - euler_gamma*(x-1) + (pi^2/12 + euler_gamma^2/2)*(x-1)^2")
    );
}

#[test]
fn series_of_polygamma() {
    assert_eq!(
        series("series(polygamma(1, x), x, 0, 2)"),
        series("1/x^2 + pi^2/6 - 2*zeta(3)*x")
    );
    // Asymptotic series at infinity
    assert_eq!(
        series("series(digamma(x), x, oo, 4)"),
        series("ln(x) - 1/(2*x) - 1/(12*x^2)")
    );
}

#[test]
fn series_of_exponential_integrals() {
    assert_eq!(series("series(Si(x), x, 0, 6)"), "x-1/18*(x^3)+1/600*(x^5)");
    assert_eq!(series("series(Ei(x), x, 1, 3)"), "Ei(1)+(x-1)*exp(1)");
}

/// Whole series `series(f, x, a, oo)`, printed on one line.
fn whole(input: &str) -> String {
    line(&parse!(&format!("series({input}, oo)"), R))
}

#[test]
fn whole_series() {
    let cases = [
        ("exp(x), x, 0", "sum((x^k)*(k!^-1), k, 0, oo)"),
        (
            "sin(x), x, 0",
            "sum((x^(2*k+1))*((2*k+1)!^-1)*((-1)^k), k, 0, oo)",
        ),
        (
            "cos(x), x, 0",
            "sum((x^(2*k))*((2*k)!^-1)*((-1)^k), k, 0, oo)",
        ),
        // `{$4^k$}` rather than `{$2^(2k)$}`
        (
            "cos(2*x), x, 0",
            "sum((x^(2*k))*((2*k)!^-1)*((-1)^k)*(4^k), k, 0, oo)",
        ),
        (
            "atan(x), x, 0",
            "sum(((2*k+1)^-1)*(x^(2*k+1))*((-1)^k), k, 0, oo)",
        ),
        (
            "asin(x), x, 0",
            "sum(((2*k+1)^-1)*(x^(2*k+1))*(2*k)!*(k!^-2)*(4^(-k)), k, 0, oo)",
        ),
        (
            "ln(1 + x), x, 0",
            "sum((x^k)*(k^-1)*((-1)^(k+1)), k, 1, oo)",
        ),
        ("(1 + x)^a, x, 0", "sum((x^k)*binomial(a, k), k, 0, oo)"),
        ("1/(1 + x^2), x, 0", "sum((x^(2*k))*((-1)^k), k, 0, oo)"),
        (
            "1/((1 - x)*(1 - 2*x)), x, 0",
            "sum(-(x^k)+(x^k)*(2^(k+1)), k, 0, oo)",
        ),
        ("exp(x), x, 1", "sum(((x-1)^k)*exp(1)*(k!^-1), k, 0, oo)"),
        // Laurent series, and at infinity
        ("exp(x)/x, x, 0", "sum((x^k)*((k+1)!^-1), k, -1, oo)"),
        ("1/(x - 1), x, oo", "sum(x^(-k), k, 1, oo)"),
        // Nested radicals, by the differential equation of the algebraic function
        (
            "sqrt(1 + sqrt(1 + x)), x, 0",
            "sum(-((4*k-1)^-1)*(x^k)*((2*k)!^-2)*(4*k)!*((-1)^k)*(2^(-4*k+1/2)), k, 0, oo)",
        ),
    ];
    for (f, expected) in cases {
        assert_eq!(whole(f), expected, "{f}");
    }
    // Sums of series with different general terms
    assert_eq!(
        whole("exp(x) + sin(x), x, 0"),
        "sum((x^k)*(k!^-1), k, 0, oo)+sum((x^(2*k+1))*((2*k+1)!^-1)*((-1)^k), k, 0, oo)"
    );
    // Only proven general terms: `{$x^40$}` breaks the recurrence of `{$e^x$}`
    assert_eq!(
        whole("exp(x) + x^40, x, 0"),
        "x^40+sum((x^k)*(k!^-1), k, 0, oo)"
    );
    // A Puiseux series with nested radicals, proven in the tower of its radicals
    assert_eq!(
        line(&parse!("series(sqrt(1 + sqrt(x)), x, 0, oo, 1)", R)),
        "sum(-((2*k-1)^-1)*(x^(1/2*k))*(2*k)!*(k!^-2)*((-1)^k)*(4^(-k)), k, 0, oo)"
    );
    // Rational terms of a sum split into partial fractions, and a polynomial factor distributed
    assert!(!whole("-sin(x) + 1/((4 - x)*(3 + x)), x, 0").contains("series"));
    assert!(!whole("(x/2 + 1)*atan(2*x), x, 0").contains("series"));
    // Without a common recurrence, the guess over parameters (here `{$sqrt(pi)$}`) fails fast
    assert!(!whole("erf(x) + exp(x), x, 0").contains("series"));
    // Finite series, and series without a hypergeometric general term
    assert_eq!(whole("x^2 + 1, x, 0"), "x^2+1");
    assert_eq!(whole("tan(x), x, 0"), "series(tan(x), x, 0, oo)");
    assert_eq!(whole("abs(x), x, 0"), "series(abs(x), x, 0, oo)");
    // Proofs which can't be done stay unevaluated
    assert_eq!(
        whole("x*exp(x^2)*cos(x), x, 0"),
        "series(x*exp(x^2)*cos(x), x, 0, oo)"
    );
    // Irrational poles, Fibonacci numbers by Binet's formula
    assert_eq!(
        whole("1/(1 - x - x^2), x, 0"),
        "sum((1/10*(5^(1/2)+5)*((1/2*(5^(1/2))+1/2)^k)+1/10*(-(5^(1/2))+5)*((-1/2*(5^(1/2))+1/2)^k))*(x^k), k, 0, oo)"
    );
    // Complex poles without a period
    assert_eq!(
        whole("1/(1 - x + 2*x^2), x, 0"),
        "series((-x+2*(x^2)+1)^-1, x, 0, oo)"
    );
}
