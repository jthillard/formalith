//! Expressions over the complex numbers.
use formalith::{
    field::{complex::C, real::R},
    parse,
    parser::environment::Environment,
    term::{Expand, Term},
};

use crate::common::{line, pretty};

fn eval(input: &str) -> String {
    line(&parse!(input, C))
}

#[test]
fn values_are_printed() {
    assert_eq!(eval("i"), "i");
    assert_eq!(eval("-i"), "-i");
    assert_eq!(eval("2*i"), "2*i");
    assert_eq!(eval("1+2*i"), "1+2*i");
    assert_eq!(eval("1/2-i"), "1/2-i");
    assert_eq!(eval("3"), "3");
}

#[test]
fn printed_values_are_parsed_back() {
    for input in ["i", "-i", "1+2*i", "1/2-3/4*i", "(1+i)*x", "x^(2*i)"] {
        let printed = eval(input);
        assert_eq!(eval(&printed), printed, "{input}");
    }
}

#[test]
fn compound_values_are_grouped() {
    assert_eq!(eval("(1+i)*x"), "(1+i)*x");
    assert_eq!(eval("x^(1+i)"), "x^(1+i)");
    assert_eq!(eval("(2*i)^(1/3)"), "(2*i)^(1/3)");
    assert_eq!(pretty(&parse!("(1+i)*x", C)), "(1 + i)⋅x");
}

#[test]
fn arithmetic() {
    assert_eq!(parse!("i^2", C), (-1).into());
    assert_eq!(parse!("i*i", C), (-1).into());
    assert_eq!(parse!("(1+i)*(1-i)", C), 2.into());
    assert_eq!(eval("1/(1+i)"), "1/2-1/2*i");
    assert_eq!(eval("i^-1"), "-i");
    assert_eq!(parse!("(1+i)^4", C), (-4).into());
    assert_eq!(eval("(2+3*i)-(2+i)"), "2*i");
    assert_eq!(eval("i*x+i*x"), "2*i*x");
}

#[test]
fn singular_values_are_undefined() {
    for input in [
        "ln(0)",
        "tan(pi/2)",
        "gamma(0)",
        "1/0",
        "i*undefined",
        "exp(i/0)",
    ] {
        assert_eq!(eval(input), "undefined", "{input}");
    }
    assert_eq!(eval("ln(-1)"), "i*pi");
}

#[test]
fn roots() {
    assert_eq!(eval("(-4)^(1/2)"), "2*i");
    assert_eq!(eval("(-4)^(3/2)"), "-8*i");
    assert_eq!(eval("(-4)^(-1/2)"), "-1/2*i");
    assert_eq!(parse!("4^(1/2)", C), 2.into());
    assert_eq!(eval("2^(1/2)"), "2^(1/2)");
}

#[test]
fn builtins() {
    assert_eq!(parse!("abs(3+4*i)", C), 5.into());
    assert_eq!(eval("abs(1+i)"), "2^(1/2)");
    assert_eq!(eval("re(3+4*i)"), "3");
    assert_eq!(eval("im(3+4*i)"), "4");
    assert_eq!(eval("conj(3+4*i)"), "3-4*i");
    assert_eq!(parse!("re(x+2+i)", C), parse!("re(x)+2", C));
    assert_eq!(parse!("re(i*x)", C), parse!("-im(x)", C));
    assert_eq!(
        parse!("conj((1+i)*x*y)", C),
        parse!("(1-i)*conj(x)*conj(y)", C)
    );
    assert_eq!(parse!("det([[i, 1], [1, i]])", C), (-2).into());
}

#[test]
fn expand_factor_simplify() {
    assert_eq!(parse!("(x+i)^2", C).expand(), parse!("x^2+2*i*x-1", C));
    assert_eq!(parse!("(i*x)^2", C).expand(), parse!("-x^2", C));
    assert_eq!(parse!("expand((x+i)*(x-i))", C), parse!("x^2+1", C));
    assert_eq!(parse!("(x^2-1)/(x-1)", C).simplify(), parse!("x+1", C));
    assert_eq!(parse!("(x+1)/((x+1)/x)", C).simplify(), parse!("x", C));
    assert_eq!(parse!("2*x/(4*x+2)", C).simplify(), parse!("x/(2*x+1)", C));
    assert_eq!(parse!("(2*i*y)^2", C), parse!("-4*y^2", C));
    assert_eq!(
        parse!("(x+i*y)^2 - (x-i*y)^2", C).expand(),
        parse!("4*i*x*y", C)
    );
    assert_eq!(parse!("factor(x^2-1)", C), parse!("(x+1)*(x-1)", C));
}

#[test]
fn factor_over_gaussian_rationals() {
    assert_eq!(parse!("factor(x^2+1)", C), parse!("(x-i)*(x+i)", C));
    assert_eq!(
        parse!("factor(x^4-1)", C),
        parse!("(x-i)*(x-1)*(x+1)*(x+i)", C)
    );
    assert_eq!(parse!("factor(x^2+y^2)", C), parse!("(x+i*y)*(x-i*y)", C));
    assert_eq!(parse!("factor(x^2-2*i*x-1)", C), parse!("(x-i)^2", C));
    assert_eq!(
        parse!("factor((1+i)*x^2+2*i*x)", C),
        parse!("(1+i)*x*(x+1+i)", C)
    );
    assert_eq!(parse!("factor(2*x^2+2)", C), parse!("2*(x-i)*(x+i)", C));
    assert_eq!(parse!("factor(x^2+x+1)", C), parse!("x^2+x+1", C));
}

#[test]
fn terms_differing_by_complex_constants_have_a_fixed_order() {
    assert_eq!(
        parse!("1/(x-i) + 1/(x+i)", C),
        parse!("1/(x+i) + 1/(x-i)", C)
    );
    assert_eq!(
        parse!("a*(x+2*i) + b*(x+i)", C),
        parse!("b*(x+i) + a*(x+2*i)", C)
    );
    assert_eq!(
        parse!("(x+i)*(x-i)*(x+1+i)", C),
        parse!("(x+1+i)*(x-i)*(x+i)", C)
    );
}

#[test]
fn partial_fractions_over_gaussian_rationals() {
    assert_eq!(
        parse!("apart(1/(x^2+1))", C),
        parse!("i/(2*(x+i)) - i/(2*(x-i))", C)
    );
    assert_eq!(
        parse!("apart((x+1)/(x^2*(x-1)), x)", C),
        parse!("- 1/x^2 - 2/x + 2/(x-1)", C)
    );
    // Gaussian coefficients and polynomial part
    assert_eq!(
        parse!("apart(1/((x-i)*(x+1)))", C),
        parse!("-(1-i)/(2*(x+1)) + (1-i)/(2*(x-i))", C)
    );
    assert_eq!(
        parse!("apart(x^3/(x-i))", C),
        parse!("-i/(x-i) - 1 + i*x + x^2", C)
    );
    // Irreducible over `QQ(i)`
    assert_eq!(parse!("apart(1/(x^2-2))", C), parse!("1/(x^2-2)", C));
    // Symbolic coefficients aren't supported
    assert!(matches!(
        parse!("apart(a/(x^2+1), x)", C),
        formalith::term::Term::Fun(_)
    ));
}

#[test]
fn powers_of_i() {
    assert_eq!(eval("i^3"), "-i");
    assert_eq!(eval("i^4"), "1");
    assert_eq!(eval("i^100"), "1");
    assert_eq!(eval("i^101"), "i");
    assert_eq!(eval("1/i"), "-i");
    assert_eq!(eval("i*i*x"), "-x");
    assert_eq!(eval("0*i"), "0");
    assert_eq!(parse!("(1+i)^8", C), 16.into());
    assert_eq!(eval("(1+i)/(1-i)"), "i");
    assert_eq!(parse!("(2+3*i)*(2-3*i)", C), 13.into());
}

#[test]
fn square_roots_of_negative_values() {
    assert_eq!(eval("sqrt(-1)"), "i");
    assert_eq!(eval("sqrt(-4)"), "2*i");
    assert_eq!(eval("sqrt(i)"), "i^(1/2)");
}

#[test]
fn complex_polynomials() {
    assert_eq!(parse!("expand((x+i)*(x-i))", C), parse!("x^2+1", C));
    assert_eq!(parse!("factor(x^2+1)", C), parse!("(x-i)*(x+i)", C));
}

#[test]
fn complex_factors_are_printed_with_their_sign() {
    assert_eq!(eval("factor(x^2+1)"), "(x-i)*(x+i)");
}

#[test]
fn euler_identity_and_involutions() {
    assert_eq!(parse!("exp(i*pi)", C), (-1).into());
    assert_eq!(parse!("conj(conj(x))", C), parse!("x", C));
}

#[test]
fn cosine_integral_of_negative_values() {
    // The principal value `{$"Ci"(-x) = "Ci"(x) + i pi$}`
    assert_eq!(parse!("Ci(-2)", C), parse!("Ci(2) + i*pi", C));
    assert_eq!(parse!("Ci(3)", C), parse!("Ci(3)", C));
}

#[test]
fn integrals_of_real_and_imaginary_parts() {
    assert_eq!(
        eval("integrate(exp(-x)*exp(-2*i*pi*x*t), x, 0, oo)"),
        eval("1/(1 + 2*i*pi*t)")
    );
    assert_eq!(
        eval("integrate(exp(-abs(x))*exp(-2*i*pi*x*t), x, -oo, oo)"),
        eval("2/(4*pi^2*t^2 + 1)")
    );
    assert_eq!(eval("integrate(exp(i*x), x, 0, pi)"), "2*i");
    assert_eq!(eval("integrate(x*e^(i*x), x, 0, 2*pi)"), eval("-2*i*pi"));
    assert_eq!(
        eval("integrate(1/(x+i), x)"),
        eval("ln(x^2+1)/2 - i*atan(x)")
    );
    assert_eq!(eval("integrate(exp(i*x), x)"), eval("sin(x) - i*cos(x)"));
    // No limit at infinity
    assert_eq!(eval("integrate(exp(i*x), x, 0, oo)"), "undefined");
    // Real integrands keep their infinite values
    assert_eq!(eval("integrate(1, x, 0, oo)"), "+oo");
    let mut env = Environment::new();
    env.eval("assume(a > 0)", R).unwrap();
    assert_eq!(
        line(&parse!("integrate(exp(-a*x)*exp(i*x), x, 0, oo)", C, &env)),
        eval("1/(a - i)")
    );
}

#[test]
fn limits_and_series_of_real_and_imaginary_parts() {
    assert_eq!(eval("lim((exp(i*x)-1)/x, x, 0)"), "i");
    assert_eq!(eval("lim(exp(i*x), x, oo)"), "undefined");
    assert_eq!(
        eval("series(exp(i*x), x, 0, 3)"),
        eval("1 + i*x - x^2/2 + o(x^2)")
    );
    // Non-real points are unsupported
    assert_eq!(eval("lim(x, x, i)"), "lim(x, x, i)");
}

#[test]
fn whole_series() {
    // A single sum with the imaginary unit as a parameter
    assert_eq!(
        eval("series(exp(i*x), x, 0, oo)"),
        eval("sum(x^k*i^k/k!, k, 0, oo)")
    );
    assert_eq!(
        eval("series(1/(1 - i*x), x, 0, oo)"),
        eval("sum(x^k*i^k, k, 0, oo)")
    );
    assert_eq!(
        eval("series(exp((1 + i)*x), x, 0, oo)"),
        eval("sum(x^k*(1 + i)^k/k!, k, 0, oo)")
    );
    // Otherwise the series of each part
    assert_eq!(
        eval("series(exp(x) + i*x, x, 0, oo)"),
        eval("i*x + sum(x^k/k!, k, 0, oo)")
    );
    assert_eq!(
        eval("approx(subs(series(sqrt(1 + i*x), x, 0, oo), x, 1/2))"),
        eval("approx(sqrt(1 + i/2))")
    );
    // Held sums in `C` are evaluated, differentiated and approximated
    assert_eq!(
        eval("approx(subs(series(x*exp(i*x), x, 0, oo), x, 2))"),
        eval("approx(2*exp(2*i))")
    );
    assert_eq!(
        eval("diff(series(exp(i*x), x, 0, oo), x)"),
        eval("sum(x^k*i^(k + 1)/k!, k, 0, oo)")
    );
    assert_eq!(
        eval("approx(subs(integrate(series(exp(i*x), x, 0, oo), x), x, 1))"),
        eval("approx(sin(1) + i*(1 - cos(1)))")
    );
}

#[test]
fn sums_print_negative_imaginary_terms_with_a_minus_sign() {
    assert_eq!(pretty(&parse!("x - i", C)), "x - i");
    assert_eq!(pretty(&parse!("x - 2*i*y", C)), "x - 2⋅i⋅y");
}

#[test]
fn argument() {
    for (input, expected) in [
        ("arg(1+i)", "1/4*pi"),
        ("arg(-1+i)", "3/4*pi"),
        ("arg(-1-i)", "-3/4*pi"),
        ("arg(i)", "1/2*pi"),
        ("arg(-i)", "-1/2*pi"),
        ("arg(-3)", "pi"),
        ("arg(2)", "0"),
        ("arg(0)", "undefined"),
        ("arg(1+3^(1/2)*i)", "1/3*pi"),
        ("arg(-1-3^(1/2)*i)", "-2/3*pi"),
        ("arg(x+i*y)", "arg(x+i*y)"),
        ("arg(exp(i))", "1"),
        ("arg(exp(2*i))", "2"),
        ("arg(exp(4*i))", "-2*pi+4"),
        ("arg(3*exp(-5*i))", "2*pi-5"),
    ] {
        assert_eq!(eval(input), expected, "{input}");
    }
    assert_eq!(line(&parse!("arg(-2)", R)), "pi");
    assert_eq!(line(&parse!("arg(x)", R)), "arg(x)");
    let mut env = Environment::new();
    env.eval("assume(x > 0)", C).unwrap();
    assert_eq!(
        line(&parse!("arg(x+i*y)", C, &env)),
        line(&parse!("atan(y/x)", C))
    );
    assert_eq!(line(&parse!("arg(-x)", R, &env)), "pi");
}

#[test]
fn principal_logarithm() {
    for (input, expected) in [
        ("ln(-1)", "i*pi"),
        ("ln(i)", "1/2*i*pi"),
        ("ln(-i)", "-1/2*i*pi"),
        ("ln(-2)", "i*pi+ln(2)"),
        ("ln(1+i)", "1/4*i*pi+1/2*ln(2)"),
        ("ln(3+4*i)", "i*atan(4/3)+ln(5)"),
        ("ln(exp(i))", "i"),
        ("ln(exp(2+3*i))", "2+3*i"),
        ("ln(2)", "ln(2)"),
        ("ln(x)", "ln(x)"),
    ] {
        assert_eq!(eval(input), line(&parse!(expected, C)), "{input}");
    }
}

#[test]
fn parts_of_constants() {
    for (input, expected) in [
        ("re(exp(i))", "cos(1)"),
        ("im(exp(1+i))", "exp(1)*sin(1)"),
        ("conj(exp(i))", "cos(1)-i*sin(1)"),
        ("abs(exp(i))", "1"),
        ("re(ln(-1))", "0"),
        ("re(x)", "re(x)"),
    ] {
        assert_eq!(eval(input), line(&parse!(expected, C)), "{input}");
    }
}

#[test]
fn approximations() {
    for (input, expected) in [
        ("approx(exp(1+i))", "1.46869393991589+2.28735528717884*i"),
        ("approx(1/3+i/7)", "0.333333333333333+0.142857142857143*i"),
        ("approx(ln(i))", "1.5707963267949*i"),
        ("approx(sqrt(i))", "0.707106781186548+0.707106781186548*i"),
        ("approx((-8)^(1/3))", "1.0+1.73205080756888*i"),
        ("approx(exp(i), 5)", "0.5403+0.84147*i"),
        ("approx(2)", "2.0"),
    ] {
        assert_eq!(eval(input), expected, "{input}");
    }
    assert_eq!(
        eval("approx(x+exp(i))"),
        "x+0.54030230586814+0.841470984807897*i"
    );
}

#[test]
fn rationalized_denominators() {
    assert_eq!(parse!("1/(1+i*sqrt(2))", C), parse!("(1-i*sqrt(2))/3", C));
    assert_eq!(parse!("1/(sqrt(2)+i)", C), parse!("(sqrt(2)-i)/3", C));
    assert_eq!(parse!("(1+i*sqrt(3))^2", C), parse!("2*(i*sqrt(3)-1)", C));
    assert_eq!(parse!("sqrt(2)*(1+i*sqrt(2))", C), parse!("sqrt(2)+2*i", C));
    // Real radicals have the forms of `{$RR$}`
    assert_eq!(eval("1/(1+sqrt(2))"), line(&parse!("1/(1+sqrt(2))", R)));
    for z in ["1+i*sqrt(2)", "sqrt(2)+i*3^(1/3)", "i+sqrt(2+sqrt(2))"] {
        let z = parse!(z, C);
        assert!(!matches!(z.inv(), Term::Pow(_)), "{z}");
        assert_eq!((&z * &z.inv()).expand(), parse!("1", C), "{z}");
    }
}
