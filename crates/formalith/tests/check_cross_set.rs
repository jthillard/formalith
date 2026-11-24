//! The same integer expression evaluated in `Z`, `R`, `C` and `Z/n` gives compatible values: equal in `Z`, `R`
//! and `C`, and the `Z` value reduced modulo `n` in `Z/n`.

use crate::common::{
    harness::{Verdict, check_all, fuzz},
    numeric::eval_in,
    random,
    rng::Rng,
};
use formalith::{dynamic::SetChoice, parser::environment::Environment};
use malachite::Integer;
use std::str::FromStr;

/// Moduli of the `Z/n` evaluations.
const MODULI: [u64; 4] = [2, 7, 12, 1_000_000_007];

/// Check that the expression `input` without variables has the same value in every set.
fn consistent(input: &str) -> Verdict {
    let value = |set: SetChoice| eval_in(set, &mut Environment::new(), input);
    let z = match value(SetChoice::Z) {
        Ok(z) => z,
        Err(e) => return Verdict::Skip(e),
    };
    let Ok(zi) = Integer::from_str(&z) else {
        return Verdict::Skip(format!("not an integer in Z: {z}"));
    };
    // Unevaluated builtins (`factorial` in `C`, printed `n!`...) aren't compared
    let unevaluated = |v: &Result<String, String>| v.as_ref().is_ok_and(|v| v.contains(['(', '!']));
    for set in [SetChoice::R, SetChoice::C] {
        match value(set) {
            Ok(v) if v == z => {}
            v if unevaluated(&v) => {}
            other => return Verdict::Wrong(format!("{z} in Z but {other:?} in {set}")),
        }
    }
    for n in MODULI {
        let expected = {
            let r = zi.clone() % Integer::from(n);
            if r < 0 { r + Integer::from(n) } else { r }
        };
        match value(SetChoice::Zn(n)) {
            Ok(v) if v == expected.to_string() => {}
            v if unevaluated(&v) => {}
            other => {
                return Verdict::Wrong(format!(
                    "{z} in Z, so {expected} mod {n}, but {other:?} in Z/{n}"
                ));
            }
        }
    }
    Verdict::Pass
}

#[test]
fn integer_expressions() {
    check_all(
        "cross-set",
        &[
            "2^10 - 3^5*7",
            "(3 - 5)^3 * (2 + 9)^2",
            "factorial(10) - 2^20",
            "gcd(84, 120) * lcm(4, 6)",
            "(-7)^5 + 123456789",
            "2^64 + 1",
        ],
        consistent,
    );
}

/// A random polynomial in `x`, `y` at a random integer point.
fn integer_case(rng: &mut Rng) -> String {
    let p = random::polynomial(rng, &["x", "y"], 4, 4);
    let (x, y) = (rng.range(-9, 9), rng.range(-9, 9));
    let mut e = p
        .replace('x', &format!("({x})"))
        .replace('y', &format!("({y})"));
    if rng.chance(0.3) {
        e = format!("{e} * factorial({})", rng.range(0, 8));
    }
    if rng.chance(0.3) {
        e = format!("({e})^{}", rng.range(2, 3));
    }
    e
}

#[test]
#[ignore = "fuzz: random integer expressions, run with --ignored"]
fn fuzz_integer_expressions() {
    fuzz("fuzz cross-set", 100, integer_case, consistent);
}
