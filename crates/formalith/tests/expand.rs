//! Expansion, simplification, unification and factorization of expressions.
use formalith::{
    field::real::R,
    parse,
    term::{Expand, Unify},
};

#[test]
fn expand_products() {
    assert_eq!(parse!("2*(x+1)", R).expand(), parse!("2*x+2", R));
    assert_eq!(parse!("x*(x+1)", R).expand(), parse!("x^2+x", R));
    assert_eq!(parse!("-(x+1)", R).expand(), parse!("-x-1", R));
    assert_eq!(parse!("(x+2)*(x+3)", R).expand(), parse!("x^2+5*x+6", R));
    assert_eq!(
        parse!("(a+b)*(c+d)", R).expand(),
        parse!("a*c+a*d+b*c+b*d", R)
    );
    assert_eq!(parse!("(2*x)^2", R).expand(), parse!("4*x^2", R));
    assert_eq!(parse!("(x*y)^2", R).expand(), parse!("x^2*y^2", R));
}

#[test]
fn expand_powers() {
    assert_eq!(parse!("(x+1)^2", R).expand(), parse!("x^2+2*x+1", R));
    assert_eq!(parse!("(x-1)^2", R).expand(), parse!("x^2-2*x+1", R));
    assert_eq!(parse!("(x+1)^3", R).expand(), parse!("x^3+3*x^2+3*x+1", R));
    assert_eq!(
        parse!("(x+y)^3", R).expand(),
        parse!("x^3+3*x^2*y+3*x*y^2+y^3", R)
    );
    assert_eq!(
        parse!("(x+y+z)^2", R).expand(),
        parse!("x^2+y^2+z^2+2*x*y+2*x*z+2*y*z", R)
    );
    assert_eq!(
        parse!("(x+1)^5", R).expand(),
        parse!("x^5+5*x^4+10*x^3+10*x^2+5*x+1", R)
    );
    assert_eq!(parse!("(x+1)^1", R).expand(), parse!("x+1", R));
    assert_eq!(parse!("(x+1)^0", R).expand(), 1.into());
}

#[test]
fn expand_keeps_non_expandable() {
    for input in ["x", "x+y", "(x+1)^n", "(x+1)^-1", "2^(1/2)", "x^y", "5"] {
        let term = parse!(input, R);
        assert_eq!(term.expand(), term, "{input}");
    }
}

#[test]
fn expand_is_idempotent() {
    for input in ["(x+1)^3", "(a+b)*(c+d)", "(x+y+z)^2*x"] {
        let expanded = parse!(input, R).expand();
        assert_eq!(expanded.expand(), expanded, "{input}");
    }
}

#[test]
fn simplify_rational_expressions() {
    assert_eq!(parse!("x/(x+1) + 1/(x+1)", R).simplify(), 1.into());
    assert_eq!(parse!("x - (x+1)", R).simplify(), (-1).into());
    assert_eq!(parse!("(x+1)*(x-1)", R).simplify(), parse!("x^2-1", R));
    assert_eq!(
        parse!("1/(x+1) + 1/(x-1)", R).simplify(),
        parse!("2*x/(x^2-1)", R)
    );
    assert_eq!(parse!("1/x + 1/y", R).simplify(), parse!("(x+y)/(x*y)", R));
    assert_eq!(parse!("(x^2*y-y)/(x*y+y)", R).simplify(), parse!("x-1", R));
    assert_eq!(parse!("(x^2-y^2)/(x+y)", R).simplify(), parse!("x-y", R));
    assert_eq!(parse!("x/2+x/3", R).simplify(), parse!("5/6*x", R));
}

#[test]
fn simplify_nested_fractions() {
    assert_eq!(parse!("(x+1)/((x+1)/x)", R).simplify(), parse!("x", R));
    assert_eq!(
        parse!("((x+1)/(x-1))/((x+1)/x)", R).simplify(),
        parse!("x/(x-1)", R)
    );
    assert_eq!(parse!("1/(1/x+1/y)", R).simplify(), parse!("x*y/(x+y)", R));
}

#[test]
fn simplify_numeric_content() {
    assert_eq!(parse!("2*x/(4*x+2)", R).simplify(), parse!("x/(2*x+1)", R));
    assert_eq!(parse!("-2/(-4*x-2)", R).simplify(), parse!("1/(2*x+1)", R));
    assert_eq!(
        parse!("(6*x^2-6)/(4*x-4)", R).simplify(),
        parse!("3/2*x+3/2", R)
    );
}

#[test]
fn expand_cancels_terms() {
    assert_eq!(parse!("(-y)^2", R), parse!("y^2", R));
    assert_eq!(parse!("(2*y)^2", R), parse!("4*y^2", R));
    assert_eq!(parse!("(x+y)^2 - (x-y)^2", R).expand(), parse!("4*x*y", R));
    assert_eq!(parse!("x^2+x^3+2*x^2", R), parse!("3*x^2+x^3", R));
}

#[test]
fn as_fraction() {
    let (num, den) = parse!("2/3", R).as_fraction(false);
    assert_eq!((num, den), (2.into(), 3.into()));

    let (num, den) = parse!("x", R).as_fraction(false);
    assert_eq!((num, den), (parse!("x", R), 1.into()));

    let (num, den) = parse!("x^-2", R).as_fraction(false);
    assert_eq!((num, den), (1.into(), parse!("x^2", R)));

    let (num, den) = parse!("x/y + 1/2", R).as_fraction(false);
    assert_eq!((num, den), (parse!("2*x+y", R), parse!("2*y", R)));
}

#[test]
fn unify() {
    assert_eq!(parse!("x/y + 1/2", R).unify(), parse!("(2*x+y)/(2*y)", R));
    assert_eq!(parse!("x", R).unify(), parse!("x", R));
    assert_eq!(parse!("1/2", R).unify(), parse!("1/2", R));
}

#[test]
fn factor() {
    assert_eq!(parse!("x^2+2*x+1", R).factor(), parse!("(x+1)^2", R));
    assert_eq!(
        parse!("x^3-x^2-x+1", R).factor(),
        parse!("(x-1)^2*(x+1)", R)
    );
    assert_eq!(parse!("(x+1)^3", R).factor(), parse!("(x+1)^3", R));
    assert_eq!(parse!("x+1", R).factor(), parse!("x+1", R));
    assert_eq!(
        parse!("x^4-1", R).factor(),
        parse!("(x-1)*(x+1)*(x^2+1)", R)
    );
    assert_eq!(parse!("x^2-y^2", R).factor(), parse!("(x-y)*(x+y)", R));
    assert_eq!(parse!("n^2-1", R).factor(), parse!("(n-1)*(n+1)", R));
    assert_eq!(parse!("2*x^2-2", R).factor(), parse!("2*(x-1)*(x+1)", R));
    // Fractional exponents, as polynomials in a root of their base
    assert_eq!(
        parse!("x + sqrt(x)", R).factor(),
        parse!("sqrt(x)*(sqrt(x) + 1)", R)
    );
    assert_eq!(
        parse!("x^(2/3) - 1", R).factor(),
        parse!("(x^(1/3) - 1)*(x^(1/3) + 1)", R)
    );
    // Powers with symbolic exponents are variables
    assert_eq!(parse!("x^n + x", R).factor(), parse!("x^n + x", R));
    assert_eq!(parse!("x^n*y + y", R).factor(), parse!("y*(x^n + 1)", R));
    assert_eq!(
        parse!("sqrt(x) + x^n", R).factor(),
        parse!("sqrt(x) + x^n", R)
    );
}

#[test]
fn expand_removes_zero_terms() {
    assert_eq!(parse!("(x+1)*(x-1)", R).expand(), parse!("x^2-1", R));
    assert_eq!(parse!("x - (x+1)", R).expand(), (-1).into());
}

#[test]
fn simplify_cancels_common_factors() {
    assert_eq!(parse!("(x^2-1)/(x-1)", R).simplify(), parse!("x+1", R));
    assert_eq!(parse!("(x^2-1)/(x+1)", R).simplify(), parse!("x-1", R));
}

#[test]
fn expand_large_powers() {
    assert_eq!(
        parse!("expand((x+1)^10)", R),
        parse!(
            "x^10+10*x^9+45*x^8+120*x^7+210*x^6+252*x^5+210*x^4+120*x^3+45*x^2+10*x+1",
            R
        )
    );
    assert_eq!(
        parse!("expand((a+b)^3-(a-b)^3)", R),
        parse!("6*a^2*b+2*b^3", R)
    );
    assert_eq!(
        parse!("expand((x+y+z)^2)", R),
        parse!("x^2+y^2+z^2+2*x*y+2*x*z+2*y*z", R)
    );
    assert_eq!(parse!("expand((x-1)*(x^2+x+1))", R), parse!("x^3-1", R));
    assert_eq!(parse!("expand((a+b)^20 - (b+a)^20)", R), parse!("0", R));
}

#[test]
fn expand_with_radicals() {
    assert_eq!(parse!("expand((1+sqrt(2))^2)", R), parse!("3+2*sqrt(2)", R));
    assert_eq!(
        parse!("expand((sqrt(2)+sqrt(3))^4)", R),
        parse!("49+20*sqrt(6)", R)
    );
    assert_eq!(
        parse!("expand((1+sqrt(2))*(1-sqrt(2)))", R),
        parse!("-1", R)
    );
}

#[test]
fn expand_negative_powers_and_quotients() {
    assert_eq!(parse!("expand(x*(1/x+1))", R), parse!("x+1", R));
    assert_eq!(parse!("expand((x+1)^(-2))", R), parse!("1/(x^2+2*x+1)", R));
}

#[test]
fn simplify_corner_cases() {
    assert_eq!(parse!("simplify((x^3+1)/(x+1))", R), parse!("x^2-x+1", R));
    assert_eq!(parse!("simplify((x^4-1)/(x^2+1))", R), parse!("x^2-1", R));
    assert_eq!(parse!("simplify((a+b)^2-a^2-2*a*b-b^2)", R), parse!("0", R));
    assert_eq!(parse!("simplify((x^3-1)/(x-1)-x^2-x)", R), parse!("1", R));
    assert_eq!(parse!("simplify(1/(1/x))", R), parse!("x", R));
    assert_eq!(parse!("simplify(exp(x)*exp(-x))", R), parse!("1", R));
    assert_eq!(
        parse!("simplify((1/x+1/y)/(1/x-1/y))", R),
        parse!("(x+y)/(y-x)", R)
    );
    assert_eq!(parse!("simplify(0)", R), parse!("0", R));
    assert_eq!(parse!("simplify(x)", R), parse!("x", R));
}

#[test]
fn simplify_trigonometric_identities() {
    assert_eq!(parse!("simplify(sin(x)^2+cos(x)^2)", R), parse!("1", R));
    assert_eq!(
        parse!("simplify(sin(2*x)-2*sin(x)*cos(x))", R),
        parse!("0", R)
    );
    assert_eq!(parse!("simplify(cosh(x)^2-sinh(x)^2)", R), parse!("1", R));
}

#[test]
fn simplify_exponentials_of_logarithms() {
    assert_eq!(parse!("simplify(exp(2*ln(x)))", R), parse!("x^2", R));
    assert_eq!(parse!("simplify(ln(8)/ln(2))", R), parse!("3", R));
}

#[test]
fn expand_trigonometric_sums() {
    assert_eq!(
        parse!("expand(sin(x+y))", R),
        parse!("sin(x)*cos(y)+cos(x)*sin(y)", R)
    );
}

#[test]
fn factor_hard_polynomials() {
    assert_eq!(
        parse!("factor(x^12-1)", R),
        parse!("(x-1)*(x+1)*(x^2+1)*(x^2+x+1)*(x^2-x+1)*(x^4-x^2+1)", R)
    );
    assert_eq!(
        parse!("factor(x^4+4)", R),
        parse!("(x^2+2*x+2)*(x^2-2*x+2)", R)
    );
    assert_eq!(
        parse!("factor(x^6-y^6)", R),
        parse!("(x-y)*(x+y)*(x^2+x*y+y^2)*(x^2-x*y+y^2)", R)
    );
    assert_eq!(
        parse!("factor(x^3+y^3+z^3-3*x*y*z)", R),
        parse!("(x+y+z)*(x^2+y^2+z^2-x*y-x*z-y*z)", R)
    );
    assert_eq!(
        parse!("factor(x^5+x+1)", R),
        parse!("(x^2+x+1)*(x^3-x^2+1)", R)
    );
    assert_eq!(parse!("factor(x^2*y^2-1)", R), parse!("(x*y-1)*(x*y+1)", R));
    assert_eq!(
        parse!("factor(x^16-1)", R),
        parse!("(x-1)*(x+1)*(x^2+1)*(x^4+1)*(x^8+1)", R)
    );
    assert_eq!(parse!("factor(x^2/4-1)", R), parse!("1/4*(x-2)*(x+2)", R));
    // Cyclotomic polynomials Φ1, Φ2, Φ3, Φ5, Φ6, Φ10, Φ15, Φ30
    assert_eq!(
        parse!("factor(x^30-1)", R),
        parse!(
            "(x-1)*(x+1)*(x^2+x+1)*(x^2-x+1)*(x^4+x^3+x^2+x+1)*(x^4-x^3+x^2-x+1)\
             *(x^8-x^7+x^5-x^4+x^3-x+1)*(x^8+x^7-x^5-x^4-x^3+x+1)",
            R
        )
    );
}

#[test]
fn factor_irreducible_polynomials() {
    for p in [
        "x^4+1",
        "x^2-2",
        // Minimal polynomials of sqrt(2)+sqrt(3) and sqrt(2)+sqrt(3)+sqrt(5), irreducible over Q but
        // reducible modulo every prime (Swinnerton-Dyer polynomials)
        "x^4-10*x^2+1",
        "x^8-40*x^6+352*x^4-960*x^2+576",
    ] {
        assert_eq!(parse!(&format!("factor({p})"), R), parse!(p, R), "{p}");
    }
    assert_eq!(parse!("factor(0)", R), parse!("0", R));
    assert_eq!(parse!("factor(6)", R), parse!("6", R));
    assert_eq!(parse!("factor(x)", R), parse!("x", R));
}

#[test]
fn factor_cancels_opposite_factors() {
    assert_eq!(parse!("factor((a-b)^2/(b-a))", R), parse!("-(a-b)", R));
}
