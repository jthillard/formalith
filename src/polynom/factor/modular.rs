//! Dense univariate polynomials over the prime field `{$ZZ\/p ZZ$}`, and their factorization.
//!
//! Polynomials are coefficient vectors, lowest degree first, without trailing zeros: the zero polynomial is empty.

use malachite::{
    Integer, Natural,
    base::num::arithmetic::traits::{Mod, Parity, Pow},
};

/// A polynomial over `{$ZZ\/p ZZ$}`, lowest degree first.
pub type ModPoly = Vec<u64>;

/// Deterministic xorshift generator, so factorizations don't depend on a random seed.
pub struct Rng(u64);

impl Rng {
    /// Create a generator with a fixed seed.
    pub const fn new() -> Self {
        Self(0x9E37_79B9_7F4A_7C15)
    }
    /// Next pseudo-random number.
    pub const fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

const fn mul_mod(a: u64, b: u64, p: u64) -> u64 {
    ((a as u128 * b as u128) % p as u128) as u64
}

/// `a^e mod p`
pub const fn pow_scalar(mut a: u64, mut e: u64, p: u64) -> u64 {
    let mut res = 1 % p;
    while e > 0 {
        if e & 1 == 1 {
            res = mul_mod(res, a, p);
        }
        a = mul_mod(a, a, p);
        e >>= 1;
    }
    res
}

/// Inverse of `a` modulo the prime `p`.
pub const fn inv_scalar(a: u64, p: u64) -> u64 {
    pow_scalar(a, p - 2, p)
}

fn trim(mut a: ModPoly) -> ModPoly {
    while a.last() == Some(&0) {
        a.pop();
    }
    a
}

/// Degree of `a`, `None` for the zero polynomial.
pub const fn degree(a: &ModPoly) -> Option<usize> {
    a.len().checked_sub(1)
}

/// Reduce integer coefficients modulo `p`.
pub fn from_integers(a: &[Integer], p: u64) -> ModPoly {
    let modulus = Integer::from(p);
    trim(
        a.iter()
            .map(|c| u64::try_from(&c.mod_op(&modulus)).expect("Reduced coefficient fits in u64"))
            .collect(),
    )
}

/// `a + b`
pub fn add(a: &ModPoly, b: &ModPoly, p: u64) -> ModPoly {
    let mut res = vec![0; a.len().max(b.len())];
    for (i, r) in res.iter_mut().enumerate() {
        *r = (a.get(i).copied().unwrap_or(0) + b.get(i).copied().unwrap_or(0)) % p;
    }
    trim(res)
}

/// `a - b`
pub fn sub(a: &ModPoly, b: &ModPoly, p: u64) -> ModPoly {
    let mut res = vec![0; a.len().max(b.len())];
    for (i, r) in res.iter_mut().enumerate() {
        *r = (a.get(i).copied().unwrap_or(0) + p - b.get(i).copied().unwrap_or(0)) % p;
    }
    trim(res)
}

/// `a * b`
pub fn mul(a: &ModPoly, b: &ModPoly, p: u64) -> ModPoly {
    if a.is_empty() || b.is_empty() {
        return vec![];
    }
    let mut res = vec![0; a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        for (j, y) in b.iter().enumerate() {
            res[i + j] = (res[i + j] + mul_mod(*x, *y, p)) % p;
        }
    }
    trim(res)
}

/// `c * a`
pub fn scale(a: &ModPoly, c: u64, p: u64) -> ModPoly {
    trim(a.iter().map(|x| mul_mod(*x, c, p)).collect())
}

/// Euclidean division, returning quotient and remainder.
///
/// # Panics
/// Panics if `b` is zero.
pub fn div_rem(a: &ModPoly, b: &ModPoly, p: u64) -> (ModPoly, ModPoly) {
    let db = degree(b).expect("Division by zero");
    let inv = inv_scalar(b[db], p);
    let mut rem = a.clone();
    if rem.len() <= db {
        return (vec![], rem);
    }
    let mut quot = vec![0; rem.len() - db];
    for i in (db..rem.len()).rev() {
        let q = mul_mod(rem[i], inv, p);
        quot[i - db] = q;
        if q != 0 {
            for (j, y) in b.iter().enumerate() {
                rem[i - db + j] = (rem[i - db + j] + p - mul_mod(q, *y, p)) % p;
            }
        }
    }
    rem.truncate(db);
    (trim(quot), trim(rem))
}

/// Remainder of the division of `a` by `b`.
pub fn rem(a: &ModPoly, b: &ModPoly, p: u64) -> ModPoly {
    div_rem(a, b, p).1
}

/// Divide `a` by its leading coefficient.
pub fn monic(a: &ModPoly, p: u64) -> ModPoly {
    a.last()
        .map_or_else(Vec::new, |lc| scale(a, inv_scalar(*lc, p), p))
}

/// Monic gcd of `a` and `b`.
pub fn gcd(a: &ModPoly, b: &ModPoly, p: u64) -> ModPoly {
    let (mut a, mut b) = (a.clone(), b.clone());
    while !b.is_empty() {
        let r = rem(&a, &b, p);
        a = b;
        b = r;
    }
    monic(&a, p)
}

/// Extended gcd: returns `(g, s, t)` with `s*a + t*b = g`, `g` monic.
pub fn ext_gcd(a: &ModPoly, b: &ModPoly, p: u64) -> (ModPoly, ModPoly, ModPoly) {
    let (mut r0, mut r1) = (a.clone(), b.clone());
    let (mut s0, mut s1) = (vec![1], vec![]);
    let (mut t0, mut t1) = (vec![], vec![1]);
    while !r1.is_empty() {
        let (q, r) = div_rem(&r0, &r1, p);
        let s = sub(&s0, &mul(&q, &s1, p), p);
        let t = sub(&t0, &mul(&q, &t1, p), p);
        (r0, r1) = (r1, r);
        (s0, s1) = (s1, s);
        (t0, t1) = (t1, t);
    }
    let inv = r0.last().map_or(1, |lc| inv_scalar(*lc, p));
    (scale(&r0, inv, p), scale(&s0, inv, p), scale(&t0, inv, p))
}

/// Formal derivative of `a`.
pub fn derivative(a: &ModPoly, p: u64) -> ModPoly {
    trim(
        a.iter()
            .enumerate()
            .skip(1)
            .map(|(i, c)| mul_mod(*c, i as u64 % p, p))
            .collect(),
    )
}

/// `base^exponant mod modulus`
fn pow_mod(base: &ModPoly, exponant: &Natural, modulus: &ModPoly, p: u64) -> ModPoly {
    let mut res = vec![1];
    let mut base = rem(base, modulus, p);
    let mut exponant = exponant.clone();
    while exponant != 0u32 {
        if exponant.odd() {
            res = rem(&mul(&res, &base, p), modulus, p);
        }
        base = rem(&mul(&base, &base, p), modulus, p);
        exponant >>= 1u32;
    }
    rem(&res, modulus, p)
}

/// Distinct-degree factorization of a monic square-free polynomial.
///
/// Returns `(g, d)` pairs, where `g` is the product of all irreducible factors of degree `d`.
pub fn distinct_degree(f: &ModPoly, p: u64) -> Vec<(ModPoly, usize)> {
    let x = vec![0, 1];
    let mut res = vec![];
    let mut f = f.clone();
    let mut h = x.clone();
    let mut d = 0;
    while degree(&f).is_some_and(|deg| deg >= 2 * (d + 1)) {
        d += 1;
        h = pow_mod(&h, &Natural::from(p), &f, p);
        let g = gcd(&sub(&h, &x, p), &f, p);
        if degree(&g).is_some_and(|deg| deg > 0) {
            f = div_rem(&f, &g, p).0;
            h = rem(&h, &f, p);
            res.push((g, d));
        }
    }
    if let Some(deg) = degree(&f)
        && deg > 0
    {
        res.push((f, deg));
    }
    res
}

/// Cantor–Zassenhaus equal-degree splitting of a monic square-free polynomial whose irreducible factors all have degree `d`. `p` must be odd.
pub fn equal_degree(f: &ModPoly, d: usize, p: u64, rng: &mut Rng) -> Vec<ModPoly> {
    let n = degree(f).unwrap_or(0);
    if n <= d {
        return vec![f.clone()];
    }
    let exponant = (Natural::from(p).pow(d as u64) - Natural::from(1u32)) >> 1u32;
    loop {
        let a = trim((0..n).map(|_| rng.next() % p).collect());
        if degree(&a).is_none_or(|deg| deg == 0) {
            continue;
        }
        let mut g = gcd(&a, f, p);
        if degree(&g) == Some(0) {
            let b = pow_mod(&a, &exponant, f, p);
            g = gcd(&sub(&b, &vec![1], p), f, p);
        }
        if degree(&g).is_some_and(|deg| deg > 0 && deg < n) {
            let mut res = equal_degree(&g, d, p, rng);
            res.extend(equal_degree(&div_rem(f, &g, p).0, d, p, rng));
            return res;
        }
    }
}

/// Factor a monic square-free polynomial into monic irreducible factors. `p` must be odd.
pub fn factor(f: &ModPoly, p: u64, rng: &mut Rng) -> Vec<ModPoly> {
    distinct_degree(f, p)
        .into_iter()
        .flat_map(|(g, d)| equal_degree(&g, d, p, rng))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn product(factors: &[ModPoly], p: u64) -> ModPoly {
        factors.iter().fold(vec![1], |acc, f| mul(&acc, f, p))
    }

    #[test]
    fn division_identity() {
        let p = 7;
        let (a, b) = (vec![3, 0, 5, 1, 2], vec![1, 4, 1]);
        let (q, r) = div_rem(&a, &b, p);
        assert_eq!(add(&mul(&q, &b, p), &r, p), a);
        assert!(degree(&r) < degree(&b));
    }

    #[test]
    fn extended_gcd() {
        let p = 11;
        let (a, b) = (vec![1, 0, 1], vec![2, 1]);
        let (g, s, t) = ext_gcd(&a, &b, p);
        assert_eq!(g, vec![1]);
        assert_eq!(add(&mul(&s, &a, p), &mul(&t, &b, p), p), vec![1]);
    }

    #[test]
    fn factor_x4_minus_1() {
        // x^4-1 splits into linear factors modulo 5
        let p = 5;
        let f = vec![4, 0, 0, 0, 1];
        let mut factors = factor(&f, p, &mut Rng::new());
        assert_eq!(factors.len(), 4);
        assert!(factors.iter().all(|g| degree(g) == Some(1)));
        factors.sort();
        assert_eq!(product(&factors, p), f);
    }

    #[test]
    fn distinct_degrees() {
        // (x+1)(x^2+1) modulo 3, x^2+1 is irreducible
        let p = 3;
        let f = mul(&vec![1, 1], &vec![1, 0, 1], p);
        let ddf = distinct_degree(&f, p);
        assert_eq!(ddf, vec![(vec![1, 1], 1), (vec![1, 0, 1], 2)]);
        assert_eq!(factor(&f, p, &mut Rng::new()).len(), 2);
    }
}
