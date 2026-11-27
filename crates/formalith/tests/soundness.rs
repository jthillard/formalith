//! Regressions for results that were wrong rather than unevaluated: rules applied without their side conditions,
//! and exact decisions (zero tests, signs, equal bounds) taken from floating point approximations.
use formalith::{dynamic::SetChoice, parser::environment::Environment, printer::PrintOptions};

/// The result of the last statement evaluated in `set` with shared definitions, on one line.
fn eval_in(set: &str, statements: &[&str]) -> String {
    let set = set.parse::<SetChoice>().unwrap();
    let mut env = Environment::new();
    let mut result = String::new();
    for statement in statements {
        result = set.evaluate(statement, &mut env).map_or_else(
            |err| format!("error: {err}"),
            |result| result.print(PrintOptions::plain()),
        );
    }
    result
}

/// The result of `statement` in `{$RR$}`.
fn eval_r(statement: &str) -> String {
    eval_in("R", &[statement])
}

#[test]
fn expand_powers_of_products() {
    // `{$(x y)^(1/2) = 1$}` for `{$x = y = -1$}`, while `{$x^(1/2) y^(1/2)$}` would be `{$-1$}`
    assert_eq!(eval_r("expand((x*y)^(1/2))"), "(x*y)^(1/2)");
    assert_eq!(eval_r("expand((4*x*y)^(1/2))"), "2*((x*y)^(1/2))");
    assert_eq!(eval_r("expand((x^2*y)^(1/2))"), "(y^(1/2))*abs(x)");
    // Real odd roots are multiplicative
    assert_eq!(eval_r("expand((x*y)^(1/3))"), "(x^(1/3))*(y^(1/3))");
    assert_eq!(
        eval_in("R", &["assume(x > 0, y > 0)", "expand((x*y)^(1/2))"]),
        "(x^(1/2))*(y^(1/2))"
    );
}

#[test]
fn signs_of_radicals_in_roots() {
    // The discriminant `{$10^20 sqrt(2) - 141421356237309504881$}` is about `{$-0.83$}`, positive in floats
    assert_eq!(
        eval_r("solve(x^2 + 10^10*2^(1/4)*x + 141421356237309504881/4 = 0, x)"),
        "no solution"
    );
}

#[test]
fn constants_indistinguishable_from_zero() {
    // `{$sin(10^(-2000))$}` is positive, but zero at the maximum precision of approximations
    assert!(eval_r("sin(10^(-2000)) > 0").starts_with("error"));
    assert_eq!(eval_r("sin(pi) > 0"), "no solution");
}

#[test]
fn close_roots_of_inequalities() {
    // Roots within the relative accuracy of approximations aren't merged
    let bound =
        "10000000000000000000000000000000000000001/10000000000000000000000000000000000000000";
    assert_eq!(
        eval_r("(x-1)*(x-1-10^(-40)) < 0"),
        format!("x ∈ (1, {bound})")
    );
    assert_eq!(
        eval_r("(x-1)*(x-1-10^(-40)) <= 0"),
        format!("x ∈ [1, {bound}]")
    );
    assert!(eval_r("(x-sqrt(2))*(x-sqrt(2)-10^(-50)) < 0").starts_with("error"));
}

#[test]
fn close_bounds_and_poles_of_definite_integrals() {
    // Bounds and singular points equal as floats
    assert_eq!(
        eval_r("integrate(1, x, 1, 1+10^(-20))"),
        "1/100000000000000000000"
    );
    assert_eq!(eval_r("integrate(1/(x-1+10^(-13)), x, 0, 1)"), "undefined");
    // The sign of `{$|x - c|$}` on `{$(0, c)$}` from a sample point inside it
    assert_eq!(
        eval_r("integrate(abs(x - 10^(-30)), x, 0, 10^(-30))"),
        "1/2000000000000000000000000000000000000000000000000000000000000"
    );
    // A denominator negative only on `{$|x| < 1.4 dot 10^(-4)$}`, between sample points
    assert!(
        eval_r("integrate((exp(x)-1)/(exp(x)-1-x-10^(-8)), x, -1/2, 1)").starts_with("integrate(")
    );
}

#[test]
fn zero_tests_of_leading_coefficients() {
    // The leading coefficient vanishes at the points where coefficients used to be evaluated
    assert_eq!(
        eval_r("lim((x-5)*(7*x-26)*(9*x-64)*exp(x) - exp(x/2), x, oo)"),
        "+oo"
    );
}

#[test]
fn undecided_constant_equations() {
    // The constant is zero without simplifying to it, so the branch isn't dropped as without solution
    assert!(eval_r("x = cos(pi/7), 8*x^3 - 4*x^2 - 4*x + 1 = 0").starts_with("error"));
    assert_eq!(eval_r("x = 1, x^2 = 2"), "no solution");
}

#[test]
fn vanishing_symbolic_pivots() {
    // The second row is the first one over `{$x + 1$}`, the eliminated entry `{$x - 1 - (x^2 - 1)/(x + 1)$}` is zero
    let m = "[[x+1, x^2-1],[1, x-1]]";
    assert_eq!(eval_in("M", &[&format!("rank({m})")]), "1");
    assert_eq!(eval_in("M", &[&format!("kernel({m})")]), "[[-x+1],[1]]");
    assert!(!eval_in("M", &[&format!("{m}^(-1)")]).contains("0^-1"));
}

#[test]
fn roots_modulo_large_primes() {
    // The degree is above the limit of the factorization, which didn't run: 1 is a root
    assert!(eval_in("Z/65537", &["x^70000 - 1 = 0"]).starts_with("error"));
    // `{$-1$}` isn't a square modulo `{$p = 3 mod 4$}`
    assert_eq!(eval_in("Z/1000003", &["x^2 + 1 = 0"]), "no solution");
}

#[test]
fn principal_branches_in_complex_calculus() {
    // `{$RR$}` gives the real cube root `{$-2$}`, and an undefined integral where `{$sqrt(x)$}` isn't real
    assert!(eval_in("C", &["lim(x^(1/3), x, -8)"]).starts_with("lim("));
    assert!(eval_in("C", &["integrate(sqrt(x), x, -1, 0)"]).starts_with("integrate("));
    assert_eq!(eval_in("C", &["lim(ln(x), x, -1)"]), "i*pi");
    assert_eq!(eval_in("C", &["integrate(sqrt(x), x, 0, 1)"]), "2/3");
}

#[test]
fn small_oscillations_at_infinity() {
    // The result depends on the angle by less than the tolerance of its samples
    assert_eq!(eval_r("lim(10^(-30)*sin(x), x, oo)"), "undefined");
    assert_eq!(eval_r("lim(1 + 10^(-30)*sin(x), x, oo)"), "undefined");
    assert_eq!(eval_r("lim(sin(x)^2 + cos(x)^2, x, oo)"), "1");
}

#[test]
fn errors_of_approximations_are_bounded() {
    // `sin` reduces large arguments with enough digits of `{$pi$}`, and decisions use its sign
    assert_eq!(eval_r("approx(sin(10^50))"), "-0.78967249342931");
    assert_eq!(eval_r("piecewise(sin(10^50) > 0, 1, 0)"), "0");
    // A zero times a large constant has no sign, its errors being amplified too
    assert_eq!(
        eval_r("approx(10^40*(atan(1/2) + atan(1/3) - pi/4))"),
        "0.0"
    );
    // `{$4 (atan(1/2) + atan(1/3))/pi = 1$}` is at a jump of `floor`, which has no approximate value there
    assert!(
        eval_r("piecewise(floor(4*(atan(1/2) + atan(1/3))/pi) = 1, 1, 0)")
            .starts_with("piecewise(")
    );
}

#[test]
fn reduction_of_large_angles() {
    // `{$k$}` in `{$atan(tan theta) = theta - k pi$}` from an approximation of `{$theta / pi$}` accurate enough
    assert_eq!(
        eval_r("atan(tan(10^30))"),
        "-318309886183790671537767526745*pi+1000000000000000000000000000000"
    );
    assert_eq!(
        eval_r("atan(tan(10^32))"),
        "-31830988618379067153776752674503*pi+100000000000000000000000000000000"
    );
}

#[test]
fn coefficients_defined_only_at_large_points() {
    // `{$(9x - 64) ln(x - 7)$}` is only defined at `{$64/9$}` among the small test points, where it vanishes
    assert_eq!(eval_r("lim(x - exp(x)*(9*x - 64)*ln(x - 7), x, oo)"), "-oo");
}

#[test]
fn poles_near_bounds_of_definite_integrals() {
    // The pole `{$5 pi/6$}` of `{$tan(3x)$}` is `{$10^(-40)$}` inside the interval, outside of it in floats
    assert_eq!(
        eval_r("integrate(tan(3*x), x, 7, 5*pi/2 + 10^(-40))"),
        "undefined"
    );
}

#[test]
fn exceptional_values_of_closed_forms() {
    // The closed form has a pole at `{$n = 0$}`, which can't be approximated, so the value there is a case
    assert!(
        eval_r("sum(binomial(n, k)*binomial(n, k + 1), k, 0, n)")
            .starts_with("piecewise(n = 0, 0,")
    );
}

#[test]
fn zeros_need_proofs() {
    // `{$10^(-2000) sin t$}` depends on the angle, below the precision of approximations: not taken as constant
    assert!(eval_r("lim(sin(10^(-2000)*sin(x)), x, oo)").starts_with("lim("));
}
