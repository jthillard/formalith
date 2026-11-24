//! Normalization under assumptions checked numerically on the assumed domain only: with `assume(x > 0)`,
//! `sqrt(x^2) = x` must hold for positive `x`.

use crate::common::{
    harness::{Verdict, case_rng, check_all, fuzz},
    numeric::{assumed_vars, env_with, equivalent, eval, symbols},
    random,
    rng::Rng,
};

/// Check `f` against its normalization under the assumptions of `input` = `assumptions; f`.
fn assumed(input: &str) -> Verdict {
    let (assumptions, f) = input.split_once(';').unwrap();
    let mut env = env_with(&[&format!("assume({})", assumptions.trim())]);
    let f = f.trim();
    let normalized = match eval(&mut env, &format!("simplify({f})")) {
        Ok(res) => res,
        Err(e) => return Verdict::Skip(e),
    };
    let names = symbols(f);
    let names: Vec<&str> = names.iter().map(String::as_str).collect();
    let vars = assumed_vars(&env, &names);
    let mut rng = case_rng(input);
    match equivalent(&env, f, &normalized, &vars, &mut rng).into() {
        Verdict::Wrong(why) => Verdict::Wrong(format!("{f} = {normalized}: {why}")),
        verdict => verdict,
    }
}

#[test]
fn assumptions() {
    check_all(
        "assumptions",
        &[
            "x > 0; sqrt(x^2)",
            "x < 0; sqrt(x^2)",
            "x < 0; abs(x)*x",
            "x > 0; ln(abs(x))",
            "x > 0, y > 0; sqrt(4*x^2*y^2)",
            "x < 0; sqrt(9*x^2)",
            "x > 0; (2*x)^(1/3)",
            "x > 0; sign(x)*x",
            "x < 0; sign(x) + abs(x)",
            "n integer; sin(x + n*pi)",
            "n integer; cos(x + n*pi)",
            "n integer, n > 0; floor(n) + ceil(n)",
            "x != 0; x^2/abs(x)",
            "x <= 0; abs(x - 1)",
        ],
        assumed,
    );
}

/// Random assumptions on `x`, `y` and a random expression in them.
fn case(rng: &mut Rng) -> String {
    let relation = |rng: &mut Rng, v| format!("{v} {} 0", rng.pick(&[">", "<", "!=", ">=", "<="]));
    let assumptions = format!("{}, {}", relation(rng, "x"), relation(rng, "y"));
    let f = match rng.below(3) {
        0 => format!("sqrt({}^2)", random::expr(rng, &["x", "y"], 2)),
        1 => format!("abs({})", random::expr(rng, &["x", "y"], 2)),
        _ => random::expr(rng, &["x", "y"], 3),
    };
    format!("{assumptions}; {f}")
}

#[test]
#[ignore = "fuzz: random expressions under random assumptions, run with --ignored"]
fn fuzz_assumptions() {
    fuzz("fuzz assumptions", 100, case, assumed);
}
