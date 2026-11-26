//! Single-line and pretty printing.
use formalith::{
    field::{complex::C, matrix::M, real::R},
    parse,
    printer::{Print, PrintOptions},
};

use crate::common::{line, pretty, typst};

#[test]
fn print_values() {
    assert_eq!(line(&parse!("0", R)), "0");
    assert_eq!(line(&parse!("-5", R)), "-5");
    assert_eq!(line(&parse!("1/2", R)), "1/2");
    assert_eq!(line(&parse!("-1/2", R)), "-1/2");
    assert_eq!(pretty(&parse!("-5", R)), "-5");
}

#[test]
fn print_sums_and_powers() {
    assert_eq!(line(&parse!("x+1", R)), "x+1");
    assert_eq!(line(&parse!("x-1", R)), "x-1");
    assert_eq!(line(&parse!("x^2", R)), "x^2");
    assert_eq!(line(&parse!("x^-2", R)), "x^-2");
    assert_eq!(line(&parse!("(x+1)^2", R)), "(x+1)^2");
    assert_eq!(line(&parse!("(x+1)^(1/2)", R)), "(x+1)^(1/2)");
    assert_eq!(line(&parse!("x^(y+1)", R)), "x^(y+1)");
}

#[test]
fn print_functions() {
    assert_eq!(line(&parse!("abs(x)", R)), "abs(x)");
    assert_eq!(line(&parse!("foo(3)", R)), "foo(3)");
}

#[test]
fn print_matrix_terms() {
    assert_eq!(line(&parse!("[[1,x],[2,3]]", M)), "[[1,x],[2,3]]");
    assert_eq!(
        pretty(&parse!("[[1,x],[2,3]]", M)),
        "⎡1  x⎤\n⎢    ⎥\n⎣2  3⎦"
    );
}

#[test]
fn pretty_print_powers() {
    assert_eq!(pretty(&parse!("x^(y+1)", R)), " y + 1\nx     ");
    assert_eq!(pretty(&parse!("x^2", R)), " 2\nx ");
}

#[test]
fn pretty_print_roots() {
    assert_eq!(pretty(&parse!("x^(1/2)", R)), " _\n√x");
    assert_eq!(pretty(&parse!("(x+1)^(1/3)", R)), " _____\n∛x + 1");
    assert_eq!(pretty(&parse!("x^(1/n)", R)), "n _\n √x");
    assert_eq!(pretty(&parse!("1/x^(1/2)", R)), "1 \n──\n _\n√x");
    assert_eq!(pretty(&parse!("x^(2/n)", R)), "   ___\n n╱  2\n╲╱  x ");
    assert_eq!(
        pretty(&parse!("(a/b)^(1/(n+1))", R)),
        "       __\n      ╱ a\nn + 1╱  ─\n   ╲╱   b"
    );
}

#[test]
fn pretty_print_fractions() {
    assert_eq!(
        pretty(&parse!("x/2+1/(x+1)", R)),
        "x     1  \n─ + ─────\n2   x + 1"
    );
    assert_eq!(pretty(&parse!("1/x", R)), "1\n─\nx");
    assert_eq!(pretty(&parse!("(x+1)/(x-1)", R)), "x + 1\n─────\nx - 1");
    assert_eq!(
        pretty(&parse!("2*(x+1)/3", R)),
        "2⋅(x + 1)\n─────────\n    3    "
    );
}

#[test]
fn pretty_print_signs() {
    assert_eq!(pretty(&parse!("-x", R)), "-x");
    assert_eq!(pretty(&parse!("-(x+1)", R)), "-(x + 1)");
    assert_eq!(pretty(&parse!("x-2*y", R)), "x - 2⋅y");
    assert_eq!(pretty(&parse!("exp(-x)", R)), "exp(-x)");
    assert_eq!(pretty(&parse!("-x^(1/2)", R)), "  _\n-√x");
    assert_eq!(pretty(&parse!("-1/2", R)), " 1\n-─\n 2");
    assert_eq!(pretty(&parse!("-x/y", R)), " x\n-─\n y");
    assert_eq!(pretty(&parse!("-2*x/(3*y)", R)), " 2⋅x\n-───\n 3⋅y");
    assert_eq!(pretty(&parse!("(-1)^x", R)), "    x\n(-1) ");
    assert_eq!(line(&parse!("(-1)^x", R)), "(-1)^x");
}

#[test]
fn pretty_print_constants() {
    assert_eq!(pretty(&parse!("pi", R)), "π");
    assert_eq!(pretty(&parse!("2*pi", R)), "2⋅π");
    assert_eq!(pretty(&parse!("-oo", R)), "-∞");
    assert_eq!(line(&parse!("pi", R)), "pi");
    assert_eq!(line(&parse!("-oo", R)), "-oo");
}

#[test]
fn print_positive_infinity() {
    // Signed when it stands alone, not as an operand
    assert_eq!(line(&parse!("oo", R)), "+oo");
    assert_eq!(pretty(&parse!("oo", R)), "+∞");
    assert_eq!(typst(&parse!("oo", R)), "+oo");
    assert_eq!(line(&parse!("x + oo", R)), "oo+x");
    assert_eq!(pretty(&parse!("x + oo", R)), "∞ + x");
    assert_eq!(pretty(&parse!("x^oo", R)), " ∞\nx ");
    assert_eq!(pretty(&parse!("lim(1/x, x, 0, 1)", R)), "+∞");
    assert_eq!(line(&parse!("f(oo)", R)), "f(+oo)");
    // The printed form parses back
    assert_eq!(parse!(line(&parse!("oo", R)), R), parse!("oo", R));
}

#[test]
fn pretty_print_piecewise() {
    assert_eq!(
        pretty(&parse!("piecewise(x < 0, -x, x)", R)),
        "⎧ -x  if x < 0 \n⎩ x   otherwise"
    );
    assert_eq!(
        pretty(&parse!("piecewise(x < 0, -x, x > 1, x^2/2, oo)", R)),
        "⎧ -x  if x < 0 \n⎪  2           \n⎨ x            \n⎪ ──  if x > 1 \n⎪ 2            \n⎩ +∞  otherwise"
    );
    assert_eq!(
        typst(&parse!("piecewise(x < 0, -x, oo)", R)),
        "cases(-x & \"if \" x < 0, +oo & \"otherwise\")"
    );
}

#[test]
fn pretty_print_integrals() {
    assert_eq!(
        pretty(&parse!("integrate(exp(x^3), x)", R)),
        "⌠           \n⎮    ⎛ 3⎞   \n⎮ exp⎝x ⎠ dx\n⌡           "
    );
    assert_eq!(
        pretty(&parse!("integrate(f(x), x, 0, 1)", R)),
        "1        \n⌠        \n⎮ f(x) dx\n⌡        \n0        "
    );
    assert_eq!(
        pretty(&parse!("integrate(f(x)+1, x, -oo, oo)", R)),
        "+∞              \n⌠               \n⎮  (f(x) + 1) dx\n⌡               \n-∞              "
    );
    assert_eq!(
        pretty(&parse!("integrate(f(x)/x, x, 0, pi)", R)),
        "π        \n⌠        \n⎮ f(x)   \n⎮ ──── dx\n⎮  x     \n⌡        \n0        "
    );
}

#[test]
fn display_matches_pretty_print_without_colors() {
    // `Display` uses default options, which only enable colors on a terminal.
    let term = parse!("x/2+1/(x+1)", R);
    let displayed = format!("{term}");
    if !displayed.contains('\u{1b}') {
        assert_eq!(displayed, pretty(&term));
    }
}

#[test]
fn print_products() {
    assert_eq!(line(&parse!("x*y", R)), "x*y");
    assert_eq!(line(&parse!("2*x", R)), "2*x");
    assert_eq!(line(&parse!("-x", R)), "-x");
    assert_eq!(line(&parse!("x-y", R)), "x-y");
}

#[test]
fn print_typst() {
    assert_eq!(typst(&parse!("asin(x)", R)), "arcsin(x)");
    assert_eq!(typst(&parse!("atan(x)", R)), "arctan(x)");
    assert_eq!(typst(&parse!("sinh(x)", R)), "sinh(x)");
    assert_eq!(typst(&parse!("factorial(n)", R)), "n!");
    assert_eq!(typst(&parse!("factorial(n+1)", R)), "(n+1)!");
    assert_eq!(typst(&parse!("binomial(n, k)", R)), "binom(n, k)");
    assert_eq!(typst(&parse!("1/2", R)), "frac(1, 2)");
    assert_eq!(typst(&parse!("-1/2", R)), "-frac(1, 2)");
    assert_eq!(
        typst(&parse!("x/2+1/(x+1)", R)),
        "frac(1, 2) x+frac(1, x+1)"
    );
    assert_eq!(typst(&parse!("x^-2", R)), "frac(1, x^2)");
    assert_eq!(typst(&parse!("(x+1)^(1/2)", R)), "sqrt(x+1)");
    assert_eq!(typst(&parse!("x^(2/3)", R)), "root(3, x^2)");
    assert_eq!(typst(&parse!("x^(1/n)", R)), "root(n, x)");
    assert_eq!(typst(&parse!("x^(-1/2)", R)), "frac(1, sqrt(x))");
    assert_eq!(typst(&parse!("x^(y+1)", R)), "x^(y+1)");
    assert_eq!(typst(&parse!("(-2)^x", R)), "(-2)^x");
    assert_eq!(typst(&parse!("2*x*y", R)), "2 x y");
    assert_eq!(typst(&parse!("x-y", R)), "x-y");
    assert_eq!(typst(&parse!("-x/y", R)), "-frac(x, y)");
    assert_eq!(typst(&parse!("3/(x*y)", R)), "frac(3, x y)");
}

#[test]
fn print_typst_functions() {
    assert_eq!(typst(&parse!("abs(x)", R)), "abs(x)");
    assert_eq!(typst(&parse!("foo(3)", R)), "op(\"foo\")(3)");
    assert_eq!(typst(&parse!("f(x)", R)), "f(x)");
    assert_eq!(typst(&parse!("conj(x)", R)), "overline(x)");
    assert_eq!(typst(&parse!("sign(x)", R)), "op(\"sign\")(x)");
    assert_eq!(
        typst(&parse!("integrate(f(x), x, 0, 1)", R)),
        "integral_(0)^(1) f(x) dif x"
    );
    assert_eq!(
        typst(&parse!("integrate(f(x)+1, x, 0, 1)", R)),
        "integral_(0)^(1) (f(x)+1) dif x"
    );
}

#[test]
fn print_typst_gamma_functions() {
    assert_eq!(typst(&parse!("gamma(x)", R)), "Gamma(x)");
    assert_eq!(typst(&parse!("digamma(x)", R)), "psi(x)");
    assert_eq!(typst(&parse!("polygamma(2, x)", R)), "psi^((2))(x)");
    assert_eq!(typst(&parse!("zeta(s)", R)), "zeta(s)");
    assert_eq!(typst(&parse!("euler_gamma", R)), "gamma");
    assert_eq!(pretty(&parse!("euler_gamma", R)), "γ");
}

#[test]
fn print_typst_sets() {
    assert_eq!(typst(&parse!("[[1,x],[2,3]]", M)), "mat(1, x; 2, 3)");
    assert_eq!(typst(&parse!("2+3*i", C)), "2+3 i");
    assert_eq!(typst(&parse!("-i", C)), "-i");
}

#[test]
fn print_typst_has_no_colors() {
    let term = parse!("x/2+foo(x)", R);
    let printed = format!(
        "{}",
        term.with_options(PrintOptions {
            colors: true,
            typst: true,
            pretty_print: true,
        })
    );
    assert!(!printed.contains('\u{1b}'));
    assert!(!printed.contains('\n'));
}

#[test]
fn printed_expressions_are_parsed_back() {
    for input in [
        "x+y",
        "x-y",
        "-x",
        "2*x*y",
        "x^2+2*x+1",
        "(x+1)^2",
        "(x+1)*(x-1)",
        "sin(x)^2+cos(x)^2",
        "1/(x+1)",
        "x/(y*z)",
        "exp(-x^2)",
        "-(x^2)",
        "-1/2*x",
        "abs(x-1)",
        "ln(abs(x))",
        "atan(x)/x",
        "f(x, y)",
        "x^(y+1)",
        "x^-2",
        "2^x*3^y",
        "gamma(x)*polygamma(1, x)+euler_gamma",
        "zeta(s)",
    ] {
        let term = parse!(input, R);
        let printed = line(&term);
        assert_eq!(parse!(&printed, R), term, "{input} printed as {printed}");
    }
}

#[test]
fn rational_exponents_are_parsed_back() {
    for input in ["sqrt(x)", "x^(2/3)", "2^(1/2)", "(x+1)^(-1/2)"] {
        let term = parse!(input, R);
        let printed = line(&term);
        assert_eq!(parse!(&printed, R), term, "{input} printed as {printed}");
    }
}

#[test]
fn pretty_print_nested_fractions() {
    let printed = pretty(&parse!("1/(1+1/(1+1/x))", R));
    assert!(printed.lines().count() >= 3, "{printed}");
    let printed = pretty(&parse!("x^(y^z)", R));
    assert!(printed.lines().count() >= 2, "{printed}");
}

#[test]
fn print_large_numbers() {
    assert_eq!(line(&parse!("10^50", R)), format!("1{}", "0".repeat(50)));
    assert_eq!(line(&parse!("-10^-5", R)), "-1/100000");
}

#[test]
fn typst_output_of_calculus() {
    for input in [
        "integrate(f(x), x, 0, 1)",
        "lim(f(x), x, oo)",
        "series(f(x), x, 0, 3)",
        "sqrt(x)/2",
    ] {
        let printed = typst(&parse!(input, R));
        assert!(!printed.is_empty(), "{input}");
        assert!(!printed.contains('\u{1b}'), "{input}");
    }
}

#[test]
fn print_factorials() {
    assert_eq!(line(&parse!("factorial(n)", R)), "n!");
    assert_eq!(line(&parse!("factorial(x+1)", R)), "(x+1)!");
    assert_eq!(line(&parse!("factorial(n)^2", R)), "n!^2");
    assert_eq!(line(&parse!("x^factorial(n)", R)), "x^n!");
    assert_eq!(typst(&parse!("factorial(x+1)", R)), "(x+1)!");
    assert_eq!(pretty(&parse!("factorial(n)", R)), "n!");
    assert_eq!(pretty(&parse!("factorial(x+1)", R)), "(x + 1)!");
    assert_eq!(pretty(&parse!("factorial(1/3)", R)), "⎛1⎞ \n⎜─⎟!\n⎝3⎠ ");
}

#[test]
fn pretty_print_special_functions() {
    assert_eq!(pretty(&parse!("gamma(x)", R)), "Γ(x)");
    assert_eq!(pretty(&parse!("zeta(s)", R)), "ζ(s)");
    assert_eq!(pretty(&parse!("lambertw(x)", R)), "W(x)");
    assert_eq!(pretty(&parse!("polygamma(0, x)", R)), "ψ(x)");
    assert_eq!(pretty(&parse!("polygamma(1, x)", R)), " (1)   \nψ   (x)");
    assert_eq!(pretty(&parse!("floor(x)", R)), "⌊x⌋");
    assert_eq!(pretty(&parse!("ceil(x)", R)), "⌈x⌉");
    assert_eq!(pretty(&parse!("floor(x/2)", R)), "⎢x⎥\n⎢─⎥\n⎣2⎦");
    assert_eq!(pretty(&parse!("binomial(n, k)", R)), "⎛n⎞\n⎝k⎠");
}

#[test]
fn pretty_print_greek_names() {
    assert_eq!(pretty(&parse!("alpha + beta_1", R)), "α + β_1");
    assert_eq!(pretty(&parse!("phi(x)", R)), "φ(x)");
    assert_eq!(pretty(&parse!("Omega", R)), "Ω");
    assert_eq!(pretty(&parse!("alphabet", R)), "alphabet");
    assert_eq!(line(&parse!("alpha", R)), "alpha");
}

#[test]
fn pretty_print_limits_and_derivatives() {
    assert_eq!(
        pretty(&parse!("lim(f(x), x, 0)", R)),
        " lim  f(x)\nx → 0     "
    );
    assert_eq!(
        pretty(&parse!("lim(f(x), x, 0, -1)", R)),
        " lim   f(x)\nx → 0⁻     "
    );
    assert_eq!(
        pretty(&parse!("diff(f(x), x)", R)),
        "d     \n──f(x)\ndx    "
    );
    assert_eq!(
        pretty(&parse!("diff(f(x), x, 2)", R)),
        " 2     \nd      \n───f(x)\n  2    \ndx     "
    );
}
