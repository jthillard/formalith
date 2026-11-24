//! Primality and factorization of integers, for the builtins `isprime` and `factorint`.

use malachite::{
    Integer, Natural,
    base::num::{
        arithmetic::traits::{DivisibleBy, Gcd, ModPow},
        basic::traits::{NegativeOne, One, Two, Zero},
        factorization::traits::Factor,
    },
    rational::Rational,
};

use crate::polynom::factor::modular;

/// Primes below this bound are found by trial division.
const TRIAL_BOUND: u64 = 1 << 12;

/// Bases of the Miller-Rabin test, the first 13 primes, which make it deterministic below
/// `{$3.3 dot 10^24$}`.
const BASES: [u64; 13] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41];

/// Bound on the iterations of Pollard's rho algorithm for one factor.
const MAX_RHO_ITERATIONS: u64 = 1 << 20;

/// Whether `n` is prime: exact for `n` fitting in `u64` and below `{$3.3 dot 10^24$}`, a strong probable prime test
/// above.
pub fn is_prime(n: &Natural) -> bool {
    if let Ok(n) = u64::try_from(n) {
        return modular::is_prime(n);
    }
    if BASES.iter().any(|p| n.divisible_by(Natural::from(*p))) {
        return false;
    }
    let one = Natural::ONE;
    let minus_one = n - &one;
    let s = minus_one.trailing_zeros().unwrap_or(0);
    let d = &minus_one >> s;
    BASES.iter().all(|a| {
        let mut x = Natural::from(*a).mod_pow(&d, n);
        if x == one || x == minus_one {
            return true;
        }
        (1..s).any(|_| {
            x = (&x * &x) % n;
            x == minus_one
        })
    })
}

/// A non-trivial factor of the odd composite `n`, by Pollard's rho algorithm with Floyd's cycle detection. Returns
/// `None` if none is found within [`MAX_RHO_ITERATIONS`].
fn rho(n: &Natural) -> Option<Natural> {
    for c in 1..20_u64 {
        let c = Natural::from(c);
        let f = |x: &Natural| (x * x + &c) % n;
        let (mut x, mut y) = (Natural::TWO, Natural::TWO);
        let mut d = Natural::ONE;
        let mut iterations = 0;
        while d == 1 {
            x = f(&x);
            y = f(&f(&y));
            d = if x > y { &x - &y } else { &y - &x }.gcd(n);
            iterations += 1;
            if iterations > MAX_RHO_ITERATIONS {
                return None;
            }
        }
        if d != *n {
            return Some(d);
        }
    }
    None
}

/// Add the prime factors of `n` (without small factors) to `factors`, `None` if one can't be found.
fn split(n: Natural, factors: &mut Vec<Natural>) -> Option<()> {
    if n == 1 {
        return Some(());
    }
    if let Ok(small) = u64::try_from(&n) {
        for (p, e) in small.factor() {
            factors.extend(std::iter::repeat_n(Natural::from(p), e as usize));
        }
        return Some(());
    }
    if is_prime(&n) {
        factors.push(n);
        return Some(());
    }
    let d = rho(&n)?;
    let cofactor = &n / &d;
    split(d, factors)?;
    split(cofactor, factors)
}

/// The prime factorization of `{$n >= 1$}`, as primes with their exponents by increasing primes. Returns `None` if
/// a factor can't be found.
pub fn factor(n: &Natural) -> Option<Vec<(Natural, u64)>> {
    let mut rest = n.clone();
    let mut primes = vec![];
    let mut p = 2_u64;
    while p < TRIAL_BOUND && rest > 1 {
        let prime = Natural::from(p);
        while (&rest).divisible_by(&prime) {
            rest /= &prime;
            primes.push(prime.clone());
        }
        p += if p == 2 { 1 } else { 2 };
    }
    split(rest, &mut primes)?;
    primes.sort();
    let mut res: Vec<(Natural, u64)> = vec![];
    for prime in primes {
        match res.last_mut() {
            Some((last, e)) if *last == prime => *e += 1,
            _ => res.push((prime, 1)),
        }
    }
    debug_assert!(res.iter().all(|(p, _)| *p != Natural::ZERO));
    Some(res)
}

/// The rows `[p, e]` of the builtin `factorint(q)` for a non-zero rational `q`: `[-1, 1]` first when `q` is
/// negative, then the primes of its numerator and denominator by increasing primes, the latter with negative
/// exponents, and `[1, 1]` for `{$plus.minus 1$}`. Returns `None` for 0, or if a factor can't be found.
pub fn factor_rational(q: &Rational) -> Option<Vec<(Integer, i64)>> {
    if *q == 0 {
        return None;
    }
    let (numerator, denominator) = q.numerator_and_denominator_ref();
    let mut rows: Vec<(Integer, i64)> = factor(numerator)?
        .into_iter()
        .map(|(p, e)| Some((Integer::from(p), i64::try_from(e).ok()?)))
        .chain(
            factor(denominator)?
                .into_iter()
                .map(|(p, e)| Some((Integer::from(p), -i64::try_from(e).ok()?))),
        )
        .collect::<Option<_>>()?;
    rows.sort();
    if rows.is_empty() && *q > 0 {
        rows.push((Integer::ONE, 1));
    }
    if *q < 0 {
        rows.insert(0, (Integer::NEGATIVE_ONE, 1));
    }
    Some(rows)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn primality() {
        assert!(is_prime(&Natural::from(1_000_000_007_u64)));
        assert!(!is_prime(&Natural::from(561_u64)));
        // `{$2^89 - 1$}` is a Mersenne prime, `{$2^67 - 1 = 193707721 dot 761838257287$}` isn't
        let mersenne = |e: u64| (Natural::ONE << e) - Natural::ONE;
        assert!(is_prime(&mersenne(89)));
        assert!(!is_prime(&mersenne(67)));
    }

    #[test]
    #[allow(clippy::maybe_infinite_iter)]
    fn factorization() {
        let factors = |n: Natural| {
            factor(&n)
                .unwrap()
                .into_iter()
                .map(|(p, e)| (p.to_string(), e))
                .collect::<Vec<_>>()
        };
        assert_eq!(
            factors(Natural::from(360_u64)),
            [("2".into(), 3), ("3".into(), 2), ("5".into(), 1)]
        );
        assert_eq!(factors(Natural::ONE), []);
        let n = (Natural::ONE << 67_u64) - Natural::ONE;
        assert_eq!(
            factors(n),
            [("193707721".into(), 1), ("761838257287".into(), 1)]
        );
        // Two primes above `{$2^64$}`
        let p = Natural::from(18_446_744_073_709_551_557_u64) + Natural::from(1_000_u64);
        let p = (0_u64..)
            .map(|k| &p + Natural::from(k))
            .find(is_prime)
            .unwrap();
        let q = (0_u64..)
            .map(|k| Natural::from(1_000_003_u64) + Natural::from(k))
            .find(is_prime)
            .unwrap();
        let res = factor(&(&p * &q)).unwrap();
        assert_eq!(res, [(q, 1), (p, 1)]);
    }
}
