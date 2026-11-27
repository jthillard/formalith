//! Sequences checked against their definition: the terms `term(u, m)` of a recurrence of `R^N` equal those
//! computed by a naive iteration, shifts agree with terms (`{$"term"("shift"(u, s), m) = "term"(u, m + s)$}`), and
//! terms of closed forms equal the general term evaluated in `R`.

use formalith::{dynamic::SetChoice, parser::environment::Environment};

use crate::common::{
    harness::{Verdict, check_all, fuzz},
    numeric::eval_in,
    rng::Rng,
};

/// Number of terms compared.
const TERMS: i64 = 12;

/// A linear recurrence `{$u(n) = sum_i c_i u(n - i) + b n + a$}` from `{$u(s) = v_0, ...$}`.
struct Linear {
    coefficients: Vec<i64>,
    initial: Vec<i64>,
    start: i64,
    b: i64,
    a: i64,
}

impl Linear {
    /// Parse `c_1, ..., c_k; v_0, ..., v_(k-1); start; b; a`.
    fn parse(input: &str) -> Option<Self> {
        let parts: Vec<&str> = input.split(';').map(str::trim).collect();
        let list =
            |s: &str| -> Option<Vec<i64>> { s.split(',').map(|x| x.trim().parse().ok()).collect() };
        let [coefficients, initial, start, b, a] = parts.as_slice() else {
            return None;
        };
        Some(Self {
            coefficients: list(coefficients)?,
            initial: list(initial)?,
            start: start.parse().ok()?,
            b: b.parse().ok()?,
            a: a.parse().ok()?,
        })
    }

    /// The recurrence, as written in `R^N`.
    fn source(&self) -> String {
        let rule: Vec<String> = self
            .coefficients
            .iter()
            .enumerate()
            .map(|(i, c)| format!("({c}) u(n - {})", i + 1))
            .chain([format!("({}) n + ({})", self.b, self.a)])
            .collect();
        let initial: Vec<String> = self
            .initial
            .iter()
            .enumerate()
            .map(|(i, v)| format!("u({}) = {v}", self.start + i as i64))
            .collect();
        format!(
            "recurrence(u(n) = {}, {})",
            rule.join(" + "),
            initial.join(", ")
        )
    }

    /// The terms from `start` to `start + count - 1`.
    fn terms(&self, count: i64) -> Vec<i128> {
        let mut terms: Vec<i128> = self.initial.iter().map(|v| i128::from(*v)).collect();
        let k = self.coefficients.len();
        while (terms.len() as i64) < count {
            let n = self.start + terms.len() as i64;
            let value = self
                .coefficients
                .iter()
                .enumerate()
                .map(|(i, c)| i128::from(*c) * terms[terms.len() - 1 - i])
                .sum::<i128>()
                + i128::from(self.b) * i128::from(n)
                + i128::from(self.a);
            terms.push(value);
        }
        terms.truncate(count.max(k as i64) as usize);
        terms
    }
}

/// Evaluate `input` in `R^N`.
fn eval(input: &str) -> Result<String, String> {
    eval_in(
        SetChoice::Seq(
            formalith::dynamic::Coefficients::R,
            formalith::context::Symbol::new("n"),
        ),
        &mut Environment::new(),
        input,
    )
}

/// Check the terms and shifts of the linear recurrence of `input`, see [`Linear::parse`].
fn linear(input: &str) -> Verdict {
    let Some(recurrence) = Linear::parse(input) else {
        return Verdict::Skip(format!("invalid case `{input}`"));
    };
    let u = recurrence.source();
    let expected = recurrence.terms(TERMS);
    for (i, value) in expected.iter().enumerate() {
        let m = recurrence.start + i as i64;
        match eval(&format!("term({u}, {m})")) {
            Ok(res) if res == value.to_string() => {}
            Ok(res) => return Verdict::Wrong(format!("term({u}, {m}) = {res}, expected {value}")),
            Err(e) => return Verdict::Wrong(format!("term({u}, {m}): {e}")),
        }
    }
    for s in [1, 2, 3, -1] {
        let m = recurrence.start + 4;
        let (Ok(shifted), Ok(direct)) = (
            eval(&format!("term(shift({u}, {s}), {m})")),
            eval(&format!("term({u}, {})", m + s)),
        ) else {
            return Verdict::Wrong(format!("shift({u}, {s}) can't be evaluated at {m}"));
        };
        if shifted != direct {
            return Verdict::Wrong(format!(
                "term(shift({u}, {s}), {m}) = {shifted}, term({u}, {}) = {direct}",
                m + s
            ));
        }
    }
    Verdict::Pass
}

/// Check the terms of the closed form `f` against `f` evaluated in `R`.
fn closed(f: &str) -> Verdict {
    for m in 0..6 {
        let Ok(term) = eval(&format!("term({f}, {m})")) else {
            return Verdict::Skip(format!("term({f}, {m}) isn't evaluated"));
        };
        let mut env = Environment::new();
        let direct = eval_in(SetChoice::R, &mut env, &format!("chk_f(n) := {f}"))
            .and_then(|_| eval_in(SetChoice::R, &mut env, &format!("chk_f({m})")));
        match direct {
            Ok(direct) if direct == term => {}
            Ok(direct) => return Verdict::Wrong(format!("term({f}, {m}) = {term}, in R {direct}")),
            Err(e) => return Verdict::Skip(e),
        }
    }
    Verdict::Pass
}

#[test]
fn linear_recurrences() {
    check_all(
        "linear recurrences",
        &[
            "2; 1; 0; 0; 1",
            "1, 1; 0, 1; 0; 0; 0",
            "1, 1; 2, 1; 0; 0; 0",
            "0, 1; 1, 2; 3; 1; 0",
            "3, -3, 1; 1, 2, 4; 0; 0; 0",
            "-1; 5; 2; 2; -3",
            "1, 0, 0, 1; 1, 1, 1, 1; 0; 1; 1",
        ],
        linear,
    );
}

#[test]
fn closed_forms() {
    check_all(
        "closed forms",
        &[
            "n^2 + 1",
            "2^n - n",
            "(n + 1)^3 - n^3",
            "binomial(n + 2, 2)",
            "(-1)^n n",
            "factorial(n)",
        ],
        closed,
    );
}

/// A random linear recurrence of order 1 to 3, see [`Linear::parse`].
fn random_linear(rng: &mut Rng) -> String {
    let order = rng.range(1, 3) as usize;
    let list = |rng: &mut Rng, n: usize, max: i64| -> String {
        (0..n)
            .map(|_| rng.range(-max, max).to_string())
            .collect::<Vec<_>>()
            .join(", ")
    };
    let coefficients = list(rng, order, 3);
    let initial = list(rng, order, 5);
    format!(
        "{coefficients}; {initial}; {}; {}; {}",
        rng.range(-2, 3),
        rng.range(-2, 2),
        rng.range(-3, 3)
    )
}

#[test]
#[ignore = "fuzz: random linear recurrences, run with --ignored"]
fn fuzz_linear_recurrences() {
    fuzz("fuzz linear recurrences", 60, random_linear, linear);
}
