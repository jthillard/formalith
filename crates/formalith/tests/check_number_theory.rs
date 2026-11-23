//! Number theory checked against independent integer computations done here: `isprime` against trial division and
//! a deterministic Miller-Rabin test, `factorint` by multiplying its rows back with prime bases, `gcd` and `lcm`
//! against Euclid's algorithm, inverses modulo `n` by multiplying back, and `factor` modulo a prime by expanding
//! its result back.
mod common;

use common::{
    harness::{Verdict, check_all, fuzz},
    numeric::{eval_in, split_top},
    random,
    rng::Rng,
};
use formalith::parser::environment::Environment;

/// Evaluate `input` in the set named `set`.
fn eval(set: &str, input: &str) -> Result<String, String> {
    eval_in(set.parse().unwrap(), &mut Environment::new(), input)
}

/// `a b mod n` without overflow.
fn mul_mod(a: u128, b: u128, n: u128) -> u128 {
    // Operands are below `{$2^64$}`, so the product fits
    a * b % n
}

/// `a^e mod n`.
fn pow_mod(mut a: u128, mut e: u128, n: u128) -> u128 {
    let mut res = 1 % n;
    a %= n;
    while e > 0 {
        if e & 1 == 1 {
            res = mul_mod(res, a, n);
        }
        a = mul_mod(a, a, n);
        e >>= 1;
    }
    res
}

/// Whether `n < 2^64` is prime: trial division by small primes, then Miller-Rabin with the first 12 primes as
/// bases, which is deterministic below `{$3.3 dot 10^24$}`.
fn is_prime(n: u64) -> bool {
    const BASES: [u64; 12] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
    if n < 2 {
        return false;
    }
    for p in BASES {
        if n % p == 0 {
            return n == p;
        }
    }
    let n = u128::from(n);
    let (mut d, mut s) = (n - 1, 0);
    while d % 2 == 0 {
        d /= 2;
        s += 1;
    }
    'bases: for a in BASES {
        let mut x = pow_mod(u128::from(a), d, n);
        if x == 1 || x == n - 1 {
            continue;
        }
        for _ in 1..s {
            x = mul_mod(x, x, n);
            if x == n - 1 {
                continue 'bases;
            }
        }
        return false;
    }
    true
}

/// `gcd(a, b) >= 0`.
const fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// Check `isprime(n)` in `Z` and `R`.
fn isprime(input: &str) -> Verdict {
    let n: u64 = input.parse().unwrap();
    let expected = if is_prime(n) { "1" } else { "0" };
    for set in ["Z", "R"] {
        match eval(set, &format!("isprime({n})")) {
            Ok(v) if v == expected => {}
            other => {
                return Verdict::Wrong(format!(
                    "isprime({n}) = {other:?} in {set}, expected {expected}"
                ));
            }
        }
    }
    Verdict::Pass
}

/// Check `factorint(n)`: rows `[p, e]` with increasing prime bases (`-1` first for negatives), whose product is `n`.
fn factorint(input: &str) -> Verdict {
    let n: i128 = input.parse().unwrap();
    let output = match eval("M", &format!("factorint({n})")) {
        Ok(output) => output,
        Err(e) => return Verdict::Wrong(format!("factorint({n}): {e}")),
    };
    if n == 1 {
        return if output == "[[1,1]]" {
            Verdict::Pass
        } else {
            Verdict::Wrong(format!("factorint(1) = {output}"))
        };
    }
    let Some(rows) = output
        .strip_prefix('[')
        .and_then(|o| o.strip_suffix(']'))
        .map(|o| split_top(o, ','))
    else {
        return Verdict::Wrong(format!("not a matrix: {output}"));
    };
    let mut product: i128 = 1;
    let mut previous = 0i128;
    for row in rows {
        let entries = split_top(row.trim_matches(['[', ']']), ',');
        let [p, e]: [i128; 2] = match entries
            .iter()
            .map(|x| x.parse::<i128>())
            .collect::<Result<Vec<_>, _>>()
            .ok()
            .and_then(|v| v.try_into().ok())
        {
            Some(row) => row,
            None => return Verdict::Wrong(format!("bad row `{row}` in {output}")),
        };
        if p == -1 {
            if previous != 0 || e != 1 {
                return Verdict::Wrong(format!("misplaced [-1, {e}] in {output}"));
            }
        } else if p <= previous || !is_prime(p as u64) || e < 1 {
            return Verdict::Wrong(format!("bad row [{p}, {e}] in {output}"));
        }
        previous = p;
        product *= p.pow(e as u32);
    }
    if product == n {
        Verdict::Pass
    } else {
        Verdict::Wrong(format!(
            "factorint({n}) = {output}, whose product is {product}"
        ))
    }
}

/// Check `gcd(a, b)` and `lcm(a, b)` in `Z`: `a; b`.
fn gcd_lcm(input: &str) -> Verdict {
    let (a, b) = input.split_once(';').unwrap();
    let (a, b): (i128, i128) = (a.trim().parse().unwrap(), b.trim().parse().unwrap());
    let g = gcd(a, b);
    let l = if g == 0 { 0 } else { (a / g * b).abs() };
    for (name, expected) in [("gcd", g), ("lcm", l)] {
        match eval("Z", &format!("{name}({a}, {b})")) {
            Ok(v) if v == expected.to_string() => {}
            other => {
                return Verdict::Wrong(format!(
                    "{name}({a}, {b}) = {other:?}, expected {expected}"
                ));
            }
        }
    }
    Verdict::Pass
}

/// Check `a^-1` modulo `n`: `a; n`. Invertible elements have an inverse `b` with `a b = 1`, the others stay
/// unevaluated.
fn inverse(input: &str) -> Verdict {
    let (a, n) = input.split_once(';').unwrap();
    let (a, n): (i128, i128) = (a.trim().parse().unwrap(), n.trim().parse().unwrap());
    let set = format!("Z/{n}");
    let output = match eval(&set, &format!("({a})^-1")) {
        Ok(output) => output,
        Err(e) => return Verdict::Wrong(format!("({a})^-1 in {set}: {e}")),
    };
    let invertible = gcd(a, n) == 1;
    match output.parse::<i128>() {
        Ok(b) if invertible && (a * b).rem_euclid(n) == 1 % n && (0..n).contains(&b) => {
            Verdict::Pass
        }
        Ok(b) => Verdict::Wrong(format!("({a})^-1 = {b} in {set}")),
        Err(_) if !invertible => Verdict::Pass,
        Err(_) => Verdict::Wrong(format!(
            "({a})^-1 = {output} in {set}, but it is invertible"
        )),
    }
}

/// Check `factor(p)` modulo a prime: `n; p`. The factors expand back to `p`.
fn factor_mod(input: &str) -> Verdict {
    let (n, p) = input.split_once(';').unwrap();
    let set = format!("Z/{}", n.trim());
    let p = p.trim();
    let factored = match eval(&set, &format!("factor({p})")) {
        Ok(f) => f,
        Err(e) => return Verdict::Skip(e),
    };
    match eval(&set, &format!("expand(({factored}) - ({p}))")) {
        Ok(zero) if zero == "0" => Verdict::Pass,
        other => Verdict::Wrong(format!(
            "factor({p}) = {factored} in {set}, but the difference is {other:?}"
        )),
    }
}

#[test]
fn oracles() {
    assert!(is_prime(2) && is_prime(97) && is_prime(1_000_000_007));
    assert!(!is_prime(1) && !is_prime(561) && !is_prime(3_215_031_751));
    assert!(is_prime(18_446_744_073_709_551_557));
    assert_eq!(gcd(-12, 18), 6);
}

#[test]
fn curated_number_theory() {
    check_all(
        "isprime",
        &[
            "0",
            "1",
            "2",
            "97",
            "561",
            "1105",
            "1729",
            "2147483647",
            "3215031751",
            "1000000007",
            "999999999989",
            "18446744073709551557",
            "18446744073709551556",
        ],
        isprime,
    );
    check_all(
        "factorint",
        &[
            "1",
            "360",
            "-12",
            "97",
            "1024",
            "999999999989",
            "600851475143",
            "1000000016000000063",
            "-2147483648",
        ],
        factorint,
    );
    check_all(
        "gcd",
        &["12; 18", "-4; 6", "0; 5", "0; 0", "17; 31", "1071; 462"],
        gcd_lcm,
    );
    check_all(
        "inverse",
        &["3; 7", "4; 12", "5; 12", "1; 2", "123456; 1000000007"],
        inverse,
    );
    check_all(
        "factor mod p",
        &["7; x^3 + 1", "2; x^4 + x + 1", "5; x^4 - 1", "3; x^6 - 1"],
        factor_mod,
    );
}

/// A random integer, often a product of primes or a near power of two.
fn integer(rng: &mut Rng) -> u64 {
    match rng.below(4) {
        0 => rng.next_u64() % 1_000_000,
        1 => rng.next_u64() >> rng.range(0, 40),
        2 => {
            let a = (rng.next_u64() % 100_000) | 1;
            let b = (rng.next_u64() % 100_000) | 1;
            a * b
        }
        _ => (1u64 << rng.range(10, 63)) - rng.range(0, 99) as u64,
    }
}

#[test]
#[ignore = "fuzz: random integers, run with --ignored"]
fn fuzz_isprime() {
    fuzz("fuzz isprime", 300, |rng| integer(rng).to_string(), isprime);
}

#[test]
#[ignore = "fuzz: random integers, run with --ignored"]
fn fuzz_factorint() {
    fuzz(
        "fuzz factorint",
        150,
        |rng| {
            let n = i128::from(integer(rng).max(1));
            if rng.chance(0.2) { -n } else { n }.to_string()
        },
        factorint,
    );
}

#[test]
#[ignore = "fuzz: random pairs, run with --ignored"]
fn fuzz_gcd_and_inverses() {
    fuzz(
        "fuzz gcd",
        200,
        |rng| {
            format!(
                "{}; {}",
                rng.range(-10_000, 10_000),
                rng.range(-10_000, 10_000)
            )
        },
        gcd_lcm,
    );
    fuzz(
        "fuzz inverse",
        200,
        |rng| {
            let n = rng.range(2, 500);
            format!("{}; {n}", rng.range(0, n - 1))
        },
        inverse,
    );
}

#[test]
#[ignore = "fuzz: random polynomials modulo primes, run with --ignored"]
fn fuzz_factor_mod() {
    fuzz(
        "fuzz factor mod p",
        100,
        |rng| {
            let p = rng.pick(&[2, 3, 5, 7, 11, 13, 101]);
            let degree = rng.range(2, 6) as usize;
            format!("{p}; {}", random::univariate(rng, "x", degree, 9))
        },
        factor_mod,
    );
}
