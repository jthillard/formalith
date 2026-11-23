//! Polynomial rings `K[x]` checked against the definitions of their operations: `p = quo(p, q) q + rem(p, q)` with
//! `degree(rem(p, q)) < degree(q)`, `gcd(p, q)` divides `p` and `q` and leaves coprime cofactors, and
//! `gcd(p, q) lcm(p, q)` is `p q` up to a constant factor.
mod common;

use common::{
    harness::{Verdict, check_all, fuzz},
    numeric::eval_in,
    random,
    rng::Rng,
};
use formalith::{dynamic::SetChoice, parser::environment::Environment};

/// Check the operations on `input`: `set; p; q`.
fn operations(input: &str) -> Verdict {
    let parts: Vec<_> = input.split(';').map(str::trim).collect();
    let set: SetChoice = parts[0].parse().expect("a polynomial ring");
    let (p, q) = (parts[1], parts[2]);
    let eval = |s: &str| eval_in(set, &mut Environment::new(), s);
    // From the printed polynomial, since `degree` lives in the set (2 is 0 in `Z/2`)
    let degree = |s: &str| eval(s).ok().map(|v| text_degree(&v));
    let is_zero = |s: &str| eval(s).is_ok_and(|v| v == "0");
    if is_zero(q) || is_zero(p) {
        return Verdict::Skip("p or q is 0".to_owned());
    }
    let (Ok(quo), Ok(rem)) = (
        eval(&format!("quo({p}, {q})")),
        eval(&format!("rem({p}, {q})")),
    ) else {
        return Verdict::Wrong(format!("quo or rem of `{p}` by `{q}` fails"));
    };
    if !is_zero(&format!("({quo})*({q}) + ({rem}) - ({p})")) {
        return Verdict::Wrong(format!("quo = {quo}, rem = {rem}, but quo q + rem != p"));
    }
    match (degree(&rem), degree(q)) {
        (Some(r), Some(d)) if r < d => {}
        (r, d) => {
            return Verdict::Wrong(format!("degree(rem = {rem}) = {r:?} >= degree(q) = {d:?}"));
        }
    }
    let (Ok(gcd), Ok(lcm)) = (
        eval(&format!("gcd({p}, {q})")),
        eval(&format!("lcm({p}, {q})")),
    ) else {
        return Verdict::Wrong(format!("gcd or lcm of `{p}` and `{q}` fails"));
    };
    for f in [p, q] {
        if !is_zero(&format!("rem({f}, {gcd})")) {
            return Verdict::Wrong(format!("gcd = {gcd} doesn't divide {f}"));
        }
    }
    // The cofactors are coprime
    let cofactors = format!("gcd(quo({p}, {gcd}), quo({q}, {gcd}))");
    if degree(&cofactors) != Some(0) {
        return Verdict::Wrong(format!(
            "gcd = {gcd}, but the cofactors have gcd {:?}",
            eval(&cofactors)
        ));
    }
    // `{$gcd lcm = p q$}` up to a constant
    let ratio = format!("quo(({p})*({q}), ({gcd})*({lcm}))");
    if degree(&ratio) != Some(0) || !is_zero(&format!("rem(({p})*({q}), ({gcd})*({lcm}))")) {
        return Verdict::Wrong(format!(
            "gcd = {gcd}, lcm = {lcm}, but their product isn't p q up to a constant"
        ));
    }
    Verdict::Pass
}

/// The degree in `x` of a printed expanded polynomial, -1 for 0.
fn text_degree(p: &str) -> i64 {
    if p == "0" {
        return -1;
    }
    let mut degree = 0;
    let chars: Vec<char> = p.chars().collect();
    for (i, &c) in chars.iter().enumerate() {
        if c != 'x' {
            continue;
        }
        let exponent: String = if chars.get(i + 1) == Some(&'^') {
            chars[i + 2..]
                .iter()
                .take_while(|c| c.is_ascii_digit())
                .collect()
        } else {
            "1".to_owned()
        };
        degree = degree.max(exponent.parse().unwrap_or(1));
    }
    degree
}

#[test]
fn curated_polynomial_rings() {
    assert_eq!(text_degree("5*(x^2)+5*x+5"), 2);
    assert_eq!(text_degree("x^12+x"), 12);
    assert_eq!(text_degree("3"), 0);
    check_all(
        "polynomial rings",
        &[
            "R[x]; x^3 + 1; x + 2",
            "R[x]; x^2 - 1; x^2 + 2*x + 1",
            "R[x]; (x - 1)^3*(x + 2); (x - 1)*(x + 2)^2",
            "R[x]; 2*x + 2; 4*x + 4",
            "R[x]; x^5 - x; 3",
            "R[x]; 1/2*x^2 + 1/3; 2/3*x - 1",
            "Z/7[x]; x^2 - 1; x^2 + 2*x + 1",
            "Z/7[x]; 3*x^3 + 1; 2*x + 5",
            "Z/2[x]; x^4 + x + 1; x^2 + x",
            "C[x]; x^2 + 1; x - i",
        ],
        operations,
    );
}

/// Polynomials `a c` and `b c` with a common factor `c`, in a random ring.
fn case(rng: &mut Rng) -> String {
    let ring = rng.pick(&["R[x]", "R[x]", "Z/7[x]", "Z/2[x]", "Z/13[x]", "C[x]"]);
    let poly = |rng: &mut Rng| {
        let degree = rng.range(0, 3) as usize;
        random::univariate(rng, "x", degree, 5)
    };
    let (a, b, c) = (poly(rng), poly(rng), poly(rng));
    format!("{ring}; {a}*{c}; {b}*{c}")
}

#[test]
#[ignore = "fuzz: random polynomials with common factors, run with --ignored"]
fn fuzz_polynomial_rings() {
    fuzz("fuzz polynomial rings", 200, case, operations);
}
