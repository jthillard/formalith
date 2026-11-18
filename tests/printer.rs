//! Single-line and pretty printing.
use formalith::{
    field::{complex::C, matrix::M, real::R},
    parse,
    printer::{Print, PrintOptions},
};

mod common;
use common::{line, pretty, typst};

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
    assert_eq!(line(&parse!("(x+1)^(1/2)", R)), "(x+1)^1/2");
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
    assert_eq!(pretty(&parse!("2*(x+1)/3", R)), "2⋅(x + 1)\n─────────\n    3    ");
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
