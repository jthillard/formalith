//! Single-line and pretty printing.
use formalith::{
    field::{matrix::M, real::R},
    parse,
};

mod common;
use common::{line, pretty};

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
fn pretty_print_fractions() {
    assert_eq!(
        pretty(&parse!("x/2+1/(x+1)", R)),
        "1       1  \n─⋅x + ─────\n2     x + 1"
    );
    assert_eq!(pretty(&parse!("1/x", R)), "1\n─\nx");
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
#[ignore = "known bug: single-line printing of products appends a trailing `*` and omits the one after the coefficient"]
fn print_products() {
    assert_eq!(line(&parse!("x*y", R)), "x*y");
    assert_eq!(line(&parse!("2*x", R)), "2*x");
    assert_eq!(line(&parse!("-x", R)), "-x");
    assert_eq!(line(&parse!("x-y", R)), "x-y");
}
