//! Sanity checks of the self-checking helpers in `common`.
mod common;

use common::{
    harness::case_rng,
    numeric::{Check, Domain, env_with, equivalent, number},
    random,
    rng::Rng,
};

#[test]
fn equivalence_detects_equal_and_different() {
    let env = env_with(&[]);
    let vars = [("x", Domain::Any), ("y", Domain::Any)];
    let mut rng = case_rng("helpers");
    assert!(matches!(
        equivalent(&env, "(x + y)^2", "x^2 + 2*x*y + y^2", &vars, &mut rng),
        Check::Equal
    ));
    assert!(equivalent(&env, "(x + y)^2", "x^2 + x*y + y^2", &vars, &mut rng).is_differ());
    assert!(matches!(
        equivalent(&env, "sin(x)^2 + cos(x)^2", "1", &vars, &mut rng),
        Check::Equal
    ));
    // `ln` of negative values doesn't evaluate, so points are skipped
    let neg = [("x", Domain::Negative)];
    assert!(matches!(
        equivalent(&env, "ln(x)", "ln(x)", &neg, &mut rng),
        Check::Inconclusive(_)
    ));
}

#[test]
fn assumptions_restrict_sampling() {
    let env = env_with(&["assume(x > 0, n integer)"]);
    assert_eq!(Domain::assumed(&env, "x"), Domain::Positive);
    assert!(matches!(Domain::assumed(&env, "n"), Domain::Integer(..)));
    let mut rng = case_rng("assumed");
    let vars = common::numeric::assumed_vars(&env, &["x"]);
    assert!(matches!(
        equivalent(&env, "sqrt(x^2)", "x", &vars, &mut rng),
        Check::Equal
    ));
}

#[test]
fn numbers() {
    let env = env_with(&[]);
    assert_eq!(number(&env, "1/4"), Some(0.25));
    assert_eq!(number(&env, "oo"), None);
    assert_eq!(number(&env, "undefined"), None);
}

#[test]
fn generators_are_reproducible() {
    let a = random::expr(&mut Rng::new(7), &["x", "y"], 4);
    let b = random::expr(&mut Rng::new(7), &["x", "y"], 4);
    assert_eq!(a, b);
    let (m, _) = random::diagonalizable(&mut Rng::new(3), 3);
    assert!(m.starts_with("[["));
    let (p, inv) = random::unimodular(&mut Rng::new(5), 3);
    let id = random::mat_mul(&p, &inv);
    for (i, row) in id.iter().enumerate() {
        for (j, &v) in row.iter().enumerate() {
            assert_eq!(v, i64::from(i == j));
        }
    }
}
