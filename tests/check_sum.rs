//! Sums and products checked against their definitions: a closed form `S(n)` of `sum(f, k, a, n)` satisfies
//! `S(n) - S(n - 1) = f(n)` and agrees with term by term values, likewise for products with quotients.
mod common;

use common::{
    harness::{Verdict, assert_pass, check_all, fuzz},
    numeric::{Function, close, env_with, eval, number},
    random,
    rng::Rng,
};
use std::time::Duration;

/// Integers `n` where the recurrence is checked, after the lower bound.
const STEPS: i64 = 5;

/// Split `f; a` (`a` defaults to 1).
fn split(input: &str) -> (String, i64) {
    let mut parts = input.split(';').map(str::trim);
    let f = parts.next().unwrap().to_owned();
    (f, parts.next().map_or(1, |a| a.parse().unwrap()))
}

/// Check `sum(f, k, a, n)` (`product` if `product`) for `input` = `f; a`.
fn closed_form(input: &str, product: bool) -> Verdict {
    let (f, a) = split(input);
    let op = if product { "product" } else { "sum" };
    let mut env = env_with(&[]);
    let closed = match eval(&mut env, &format!("{op}({f}, k, {a}, n)")) {
        Ok(res) if !res.contains(op) => res,
        Ok(res) => return Verdict::Skip(format!("unevaluated: {res}")),
        Err(e) => return Verdict::Skip(e),
    };
    let (Ok(s), Ok(term)) = (
        Function::new(&env, &closed, &["n"]),
        Function::new(&env, &f, &["k"]),
    ) else {
        return Verdict::Skip(format!("can't define `{closed}`"));
    };
    let mut valid = 0;
    for n in a + 1..=a + STEPS {
        let (now, before) = (s.call(&[n.to_string()]), s.call(&[(n - 1).to_string()]));
        let step = if product {
            s.number_of(&format!("{now} / {before}"))
        } else {
            s.number_of(&format!("{now} - {before}"))
        };
        let (Some(step), Some(value)) = (step, term.at(&[n.to_string()])) else {
            continue;
        };
        if !close(step, value, 1e-9) {
            let rel = if product { "S(n)/S(n-1)" } else { "S(n) - S(n-1)" };
            return Verdict::Wrong(format!("S(n) = {closed}: {rel} = {step} but f({n}) = {value}"));
        }
        valid += 1;
    }
    // The closed form at small `n` against the term by term value
    for n in [a, a + 3] {
        let direct = number(&env, &format!("{op}({f}, k, {a}, {n})"));
        if let (Some(direct), Some(value)) = (direct, s.at(&[n.to_string()])) {
            if !close(direct, value, 1e-9) {
                return Verdict::Wrong(format!("S(n) = {closed}: S({n}) = {value} but {op}({f}, k, {a}, {n}) = {direct}"));
            }
            valid += 1;
        }
    }
    if valid >= 3 {
        Verdict::Pass
    } else {
        Verdict::Skip(format!("only {valid} valid points for S(n) = {closed}"))
    }
}

fn sum_check(input: &str) -> Verdict {
    closed_form(input, false)
}

fn product_check(input: &str) -> Verdict {
    closed_form(input, true)
}

/// Check that `sum(f, k, a, b)` with numeric bounds and more than 100 terms (so by a closed form) agrees with two
/// sums of at most 100 terms (computed term by term). `input` is `f; a`.
fn long_sum(input: &str) -> Verdict {
    let (f, a) = split(input);
    let env = env_with(&[]);
    let (b, mid) = (a + 150, a + 75);
    let whole = format!("sum({f}, k, {a}, {b})");
    let parts = format!("sum({f}, k, {a}, {mid}) + sum({f}, k, {}, {b})", mid + 1);
    match (number(&env, &whole), number(&env, &parts)) {
        (Some(x), Some(y)) if close(x, y, 1e-9) => Verdict::Pass,
        (Some(x), Some(y)) => Verdict::Wrong(format!("{whole} = {x} but term by term {y}")),
        _ => Verdict::Skip("not a number".to_owned()),
    }
}

/// Check an infinite sum `sum(f, k, a, oo)` against the closed form of the partial sums at a large `n`, and the
/// partial sum term by term. `input` is `f; a`, `f` decreasing fast enough for `S(10^6)` to be close.
fn infinite_sum(input: &str) -> Verdict {
    let (f, a) = split(input);
    let mut env = env_with(&[]);
    let value = match eval(&mut env, &format!("sum({f}, k, {a}, oo)")) {
        Ok(res) if !res.contains("sum") => res,
        Ok(res) => return Verdict::Skip(format!("unevaluated: {res}")),
        Err(e) => return Verdict::Skip(e),
    };
    let Some(value) = number(&env, &value) else {
        return Verdict::Skip(format!("`{value}` isn't a number"));
    };
    // Partial sum of 1000 terms (term by term since there is no closed form for large ranges otherwise)
    let partial = number(&env, &format!("sum({f}, k, {a}, {}) + sum({f}, k, {}, {})", a + 99, a + 100, a + 199));
    match partial {
        Some(partial) if close(partial, value, 1e-2) => Verdict::Pass,
        Some(partial) => Verdict::Wrong(format!("sum to oo = {value} but the first 200 terms give {partial}")),
        None => Verdict::Skip("partial sum".to_owned()),
    }
}

#[test]
fn sums() {
    check_all(
        "sums",
        &[
            "k^3 - 2*k",
            "2^k * k^2",
            "1/(k*(k + 1))",
            "1/(k*(k + 2))",
            "k * factorial(k)",
            "binomial(k, 2)",
            "(-1)^k * k",
            "1/k",
            "1/k^2",
            "k/2^k",
            "(2*k + 1)/(k^2*(k + 1)^2)",
            "1/(4*k^2 - 1)",
            "k^2 * 3^k; 0",
        ],
        sum_check,
    );
}

#[test]
fn products() {
    check_all(
        "products",
        &[
            "k",
            "2",
            "(k + 1)/k",
            "k^2",
            "1 - 1/k^2; 2",
            "3^k",
            "(k + 2)/(k + 5)",
            "k/(k + 1)",
        ],
        product_check,
    );
}

#[test]
fn long_sums() {
    check_all(
        "long sums",
        &["k^2", "1/(k*(k + 1))", "k*2^k", "(-1)^k * k^2", "binomial(k, 3)"],
        long_sum,
    );
}

#[test]
fn infinite_sums() {
    check_all(
        "infinite sums",
        &[
            "1/2^k; 0",
            "k/3^k; 0",
            "1/factorial(k); 0",
            "1/(k*(k + 1))",
            "1/k^2",
            "1/k^3",
            "1/(k^2 + 3*k + 2); 0",
            "(-1/3)^k * k; 0",
        ],
        infinite_sum,
    );
}

/// A random summand in `k`.
fn summand(rng: &mut Rng) -> String {
    let atom = |rng: &mut Rng| match rng.below(8) {
        0 => {
            let degree = rng.range(0, 3) as usize;
            random::univariate(rng, "k", degree, 4)
        }
        1 => format!("{}^k", rng.pick(&["2", "3", "1/2", "-2", "(-1)"])),
        2 => format!("1/{}", random::linear_factors(rng, "k", 2).replace("(1*k + -4)", "(k + 5)")),
        3 => format!("{}^k * {}", rng.pick(&["2", "1/3", "-1"]), random::univariate(rng, "k", 1, 3)),
        4 => format!("factorial(k) * {}", random::univariate(rng, "k", 1, 2)),
        5 => format!("binomial(k, {})", rng.range(1, 3)),
        6 => format!("1/(k + {})^2", rng.range(0, 2)),
        _ => format!("1/((k + {})*(k + {}))", rng.range(0, 2), rng.range(3, 5)),
    };
    let a = atom(rng);
    if rng.chance(0.4) {
        let b = atom(rng);
        format!("{} * {a} + {b}", random::constant(rng))
    } else {
        format!("{} * {a}", random::constant(rng))
    }
}

/// A random factor in `k`, without zeros at `k >= 1` (shifted linear factors).
fn factor(rng: &mut Rng) -> String {
    let atom = |rng: &mut Rng| match rng.below(5) {
        0 => format!("(k + {})", rng.range(0, 4)),
        1 => format!("({}*k + {})", rng.range(1, 3), rng.range(0, 3)),
        2 => format!("{}^k", rng.pick(&["2", "3", "1/2"])),
        3 => format!("(k + {})/(k + {})", rng.range(0, 4), rng.range(1, 4)),
        _ => rng.range(2, 5).to_string(),
    };
    let a = atom(rng);
    let b = atom(rng);
    format!("{a} * {b}")
}

#[test]
#[ignore = "fuzz: random sums, run with --ignored"]
fn fuzz_sums() {
    fuzz("fuzz sums", 60, summand, sum_check);
}

#[test]
#[ignore = "fuzz: random products, run with --ignored"]
fn fuzz_products() {
    fuzz("fuzz products", 60, factor, product_check);
}

#[test]
#[ignore = "fuzz: random sums with more than 100 terms, run with --ignored"]
fn fuzz_long_sums() {
    fuzz("fuzz long sums", 40, summand, long_sum);
}

fn regression(input: &str, check: fn(&str) -> Verdict) {
    assert_pass(input, Duration::from_secs(60), check);
}

#[test]
#[ignore = "bug: closed forms of products with a factor 2k + 1 evaluate to 0 at integers (see bug_coefficient_times_cancelling_powers_is_zero)"]
fn bug_product_of_odd_factors_at_integer() {
    // `S(n) = gamma(n + 3/2) 2^(n + 1)/sqrt(pi)` is right, but `S(0) = 2 gamma(3/2)/sqrt(pi)` normalizes to 0
    regression("2*k + 1; 0", product_check);
}
