//! Printing and parsing checked against each other: in every set, the plain printed result of an expression parses
//! back to the same result (the printer writes what the parser reads, and normalization is idempotent), and the
//! pretty and Typst printers don't panic.
mod common;

use common::{
    guard::no_panic,
    harness::{Verdict, assert_pass, check_all, fuzz},
    numeric::eval_in,
    random,
    rng::Rng,
};
use formalith::{dynamic::SetChoice, parser::environment::Environment};
use std::time::Duration;

/// Check the round trip of `input`: `set; expression`.
fn roundtrip(input: &str) -> Verdict {
    let (set, expr) = input.split_once(';').expect("`set; expression`");
    let set: SetChoice = match set.trim().parse() {
        Ok(set) => set,
        Err(e) => return Verdict::Wrong(format!("bad set `{set}`: {e:?}")),
    };
    let expr = expr.trim();
    let first = match eval_in(set, &mut Environment::new(), expr) {
        Ok(first) => first,
        Err(e) => return Verdict::Skip(e),
    };
    match eval_in(set, &mut Environment::new(), &first) {
        Ok(second) if second == first => {}
        Ok(second) => {
            return Verdict::Wrong(format!(
                "`{expr}` gives `{first}`, which gives `{second}` again"
            ));
        }
        Err(e) => {
            return Verdict::Wrong(format!(
                "`{expr}` gives `{first}`, which doesn't parse: {e}"
            ));
        }
    }
    for typst in [false, true] {
        if no_panic(|| set.eval(expr, typst, &mut Environment::new())).is_none() {
            let printer = if typst { "Typst" } else { "pretty" };
            return Verdict::Wrong(format!("the {printer} printer panics on `{expr}`"));
        }
    }
    Verdict::Pass
}

#[test]
fn oracle_detects_unparseable_output() {
    // An expression is its own result here, so this only checks that a pass is a pass
    assert!(matches!(roundtrip("R; x^2 + 1"), Verdict::Pass));
    assert!(matches!(roundtrip("R; 1 +"), Verdict::Skip(_)));
}

#[test]
fn curated_roundtrips() {
    check_all(
        "roundtrip",
        &[
            "R; (x + 1)^3/(x - 2)",
            "R; -x - (-y)^3",
            "R; sqrt(2)/3 + 2^(1/3)*x",
            "R; exp(-x)*sin(2*x)^2 - ln(abs(x))",
            "R; x^(-2/3) - 1/(x*y)",
            "R; atan(1/x) + factorial(x) + binomial(x, 2)",
            "R; gamma(x)*polygamma(1, x) + zeta(3)",
            "R; piecewise(x < 0, -x, x^2)",
            "R; floor(x/2) + ceil(-x) + sign(x)",
            "R; lambertw(x) + erf(x) - Si(x)",
            "R; lambertw(x, -1) + lambertw(x)",
            "R; x*rootof(x^5 - 5*x + 1, 2) - rootof(x^5 - x - 1, 1)^2",
            "R; -(-(-x))",
            "R; 2^(x + 1) - 3^(-x)",
            "Z; (x - 3)^2*(x + y)",
            "Z; gcd(12, 18)*x - factorial(5)",
            "Z/7; (3*x + 5)^3",
            "Z/12; 5*x^2 - 7*x + 11",
            "C; (1 + 2*i)*x - i*y^2",
            "C; exp(i*x)/(2 - i)",
            "R[x]; (x + 1)^4 - y*x",
            "M; [[x, 1], [2, y]]^2",
            "M; [[1, 2], [3, 4]]^-1 + I(2)",
            "M(Z); [[2, 4], [6, 8]]*[[1, 0], [1, 1]]",
        ],
        roundtrip,
    );
}

/// A random case of a random set.
fn case(rng: &mut Rng) -> String {
    match rng.below(9) {
        0..=3 => format!("R; {}", random::expr(rng, &["x", "y"], 4)),
        4 => format!("Z; {}", random::polynomial(rng, &["x", "y"], 4, 4)),
        5 => {
            let n = rng.pick(&[2, 7, 12, 1_000_000_007]);
            format!("Z/{n}; {}", random::polynomial(rng, &["x"], 4, 4))
        }
        6 => format!(
            "C; ({} + {}*i)*{} - i*{}",
            rng.range(-3, 3),
            rng.nonzero(3),
            random::polynomial(rng, &["x", "y"], 3, 3),
            random::expr(rng, &["x"], 2)
        ),
        7 => format!("R[x]; {}", random::polynomial(rng, &["x", "y"], 4, 4)),
        _ => {
            let entry = |rng: &mut Rng| random::polynomial(rng, &["x"], 2, 2);
            let m = format!(
                "[[{}, {}], [{}, {}]]",
                entry(rng),
                entry(rng),
                entry(rng),
                entry(rng)
            );
            match rng.below(3) {
                0 => format!("M; {m}^2 - {m}"),
                1 => format!("M; det({m})"),
                _ => format!("M; {m}*[[1, x], [0, 1]]"),
            }
        }
    }
}

#[test]
#[ignore = "fuzz: random expressions of every set, run with --ignored"]
fn fuzz_roundtrip() {
    fuzz("fuzz roundtrip", 300, case, roundtrip);
}

fn regression(input: &str) {
    assert_pass(input, Duration::from_secs(60), roundtrip);
}

#[test]
fn bug_leading_minus_in_matrix_sets() {
    // The scalar `{$-72 x + 7$}`, parsed from the start, was used as the operand `{$-72$}` of the product
    regression("M; -72*x + 7");
    regression("M; -2*x*y");
    regression("M; det([[1, 2*x], [3, 4]])");
}

#[test]
fn bug_products_differing_by_their_coefficient_were_equal() {
    // `{$-4 x - 3$}` and `{$-3 x - 3$}` compared equal, so sums kept the order in which they were built
    regression("R; (-4*x - 3)*(1 - 5*x) + (-3*x - 3)*(1 - 5*x) - (1 - 5*x)");
    regression("M; [[-4*x - 3, 1 - 5*x], [0, -3*x - 3]]^2 - [[-4*x - 3, 1 - 5*x], [0, -3*x - 3]]");
}
