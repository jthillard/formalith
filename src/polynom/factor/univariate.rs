//! Dense univariate polynomials over `{$ZZ$}` and `{$QQ$}`, and the Zassenhaus factorization algorithm.
//!
//! Polynomials are coefficient vectors, lowest degree first, without trailing zeros: the zero polynomial is empty.

use malachite::{
    Integer, Natural, Rational,
    base::num::{
        arithmetic::traits::{DivisibleBy, Gcd, Mod, Pow, UnsignedAbs},
        basic::traits::{One, Zero},
    },
};

use super::modular::{self, ModPoly, Rng};

/// A polynomial with integer coefficients, lowest degree first.
pub type ZPoly = Vec<Integer>;
/// A polynomial with rational coefficients, lowest degree first.
pub type QPoly = Vec<Rational>;

fn trim<C: PartialEq<u32>>(mut a: Vec<C>) -> Vec<C> {
    while a.last().is_some_and(|c| *c == 0u32) {
        a.pop();
    }
    a
}

// ---------------------------------------------------------------------------
// Integer polynomials
// ---------------------------------------------------------------------------

/// Symmetric representative of `c` modulo `m`, in `(-m/2, m/2]`.
fn smod(c: &Integer, m: &Integer) -> Integer {
    let r = c.mod_op(m);
    if Integer::from(2u32) * &r > *m {
        r - m
    } else {
        r
    }
}

fn smod_poly(a: &ZPoly, m: &Integer) -> ZPoly {
    trim(a.iter().map(|c| smod(c, m)).collect())
}

/// Inverse of `a` modulo `m`, which must be coprime.
fn inv_mod(a: &Integer, m: &Integer) -> Integer {
    let (mut r0, mut r1) = (a.mod_op(m), m.clone());
    let (mut s0, mut s1) = (Integer::ONE, Integer::ZERO);
    while r1 != 0u32 {
        let q = &r0 / &r1;
        let r = &r0 - &q * &r1;
        let s = &s0 - &q * &s1;
        (r0, r1) = (r1, r);
        (s0, s1) = (s1, s);
    }
    debug_assert!(r0 == 1u32 || r0 == -1i32);
    (s0 * r0).mod_op(m)
}

fn zadd(a: &ZPoly, b: &ZPoly) -> ZPoly {
    let zero = Integer::ZERO;
    trim(
        (0..a.len().max(b.len()))
            .map(|i| a.get(i).unwrap_or(&zero) + b.get(i).unwrap_or(&zero))
            .collect(),
    )
}

fn zsub(a: &ZPoly, b: &ZPoly) -> ZPoly {
    let zero = Integer::ZERO;
    trim(
        (0..a.len().max(b.len()))
            .map(|i| a.get(i).unwrap_or(&zero) - b.get(i).unwrap_or(&zero))
            .collect(),
    )
}

fn zmul(a: &ZPoly, b: &ZPoly) -> ZPoly {
    if a.is_empty() || b.is_empty() {
        return vec![];
    }
    let mut res = vec![Integer::ZERO; a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        for (j, y) in b.iter().enumerate() {
            res[i + j] += x * y;
        }
    }
    trim(res)
}

fn zscale(a: &ZPoly, c: &Integer) -> ZPoly {
    trim(a.iter().map(|x| x * c).collect())
}

fn from_mod(a: &ModPoly) -> ZPoly {
    a.iter().map(|c| Integer::from(*c)).collect()
}

/// Gcd of the coefficients.
pub fn content(a: &ZPoly) -> Natural {
    a.iter()
        .fold(Natural::ZERO, |acc, c| acc.gcd(c.unsigned_abs()))
}

/// Divide by the content, with a positive leading coefficient.
pub fn primitive_part(a: &ZPoly) -> ZPoly {
    let Some(lc) = a.last() else {
        return vec![];
    };
    let mut c = Integer::from(content(a));
    if *lc < 0u32 {
        c = -c;
    }
    a.iter().map(|x| x / &c).collect()
}

/// Divide `a` by `b`, returning `None` if the division isn't exact over `{$ZZ$}`.
pub fn exact_div(a: &ZPoly, b: &ZPoly) -> Option<ZPoly> {
    let db = b.len().checked_sub(1)?;
    let mut rem = a.clone();
    if rem.is_empty() {
        return Some(vec![]);
    }
    if rem.len() <= db {
        return None;
    }
    let mut quot = vec![Integer::ZERO; rem.len() - db];
    for i in (db..rem.len()).rev() {
        if rem[i] == 0u32 {
            continue;
        }
        if !(&rem[i]).divisible_by(&b[db]) {
            return None;
        }
        let q = &rem[i] / &b[db];
        for (j, y) in b.iter().enumerate() {
            rem[i - db + j] -= &q * y;
        }
        quot[i - db] = q;
    }
    rem.iter().all(|c| *c == 0u32).then(|| trim(quot))
}

// ---------------------------------------------------------------------------
// Rational polynomials
// ---------------------------------------------------------------------------

/// `a - b`
pub fn qsub(a: &QPoly, b: &QPoly) -> QPoly {
    let zero = Rational::ZERO;
    trim(
        (0..a.len().max(b.len()))
            .map(|i| a.get(i).unwrap_or(&zero) - b.get(i).unwrap_or(&zero))
            .collect(),
    )
}

/// `a * b`
pub fn qmul(a: &QPoly, b: &QPoly) -> QPoly {
    if a.is_empty() || b.is_empty() {
        return vec![];
    }
    let mut res = vec![Rational::ZERO; a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        for (j, y) in b.iter().enumerate() {
            res[i + j] += x * y;
        }
    }
    trim(res)
}

/// `c * a`
pub fn qscale(a: &QPoly, c: &Rational) -> QPoly {
    trim(a.iter().map(|x| x * c).collect())
}

/// Euclidean division, returning quotient and remainder.
///
/// # Panics
/// Panics if `b` is zero.
pub fn qdiv_rem(a: &QPoly, b: &QPoly) -> (QPoly, QPoly) {
    let db = b.len().checked_sub(1).expect("Division by zero");
    let mut rem = a.clone();
    if rem.len() <= db {
        return (vec![], rem);
    }
    let mut quot = vec![Rational::ZERO; rem.len() - db];
    for i in (db..rem.len()).rev() {
        if rem[i] == 0u32 {
            continue;
        }
        let q = &rem[i] / &b[db];
        for (j, y) in b.iter().enumerate() {
            rem[i - db + j] -= &q * y;
        }
        quot[i - db] = q;
    }
    rem.truncate(db);
    (trim(quot), trim(rem))
}

/// Extended gcd: returns `(g, s, t)` with `s*a + t*b = g`, `g` monic.
pub fn qext_gcd(a: &QPoly, b: &QPoly) -> (QPoly, QPoly, QPoly) {
    let (mut r0, mut r1) = (a.clone(), b.clone());
    let (mut s0, mut s1) = (vec![Rational::ONE], vec![]);
    let (mut t0, mut t1) = (vec![], vec![Rational::ONE]);
    while !r1.is_empty() {
        let (q, r) = qdiv_rem(&r0, &r1);
        let s = qsub(&s0, &qmul(&q, &s1));
        let t = qsub(&t0, &qmul(&q, &t1));
        (r0, r1) = (r1, r);
        (s0, s1) = (s1, s);
        (t0, t1) = (t1, t);
    }
    let inv = r0.last().map_or(Rational::ONE, |lc| Rational::ONE / lc);
    (qscale(&r0, &inv), qscale(&s0, &inv), qscale(&t0, &inv))
}

fn qderivative(a: &QPoly) -> QPoly {
    trim(
        a.iter()
            .enumerate()
            .skip(1)
            .map(|(i, c)| c * Rational::from(i))
            .collect(),
    )
}

/// Check that `a` has no repeated factor.
pub fn is_square_free(a: &QPoly) -> bool {
    qext_gcd(a, &qderivative(a)).0.len() <= 1
}

/// Write `a` as `c * z`, with `z` primitive over `{$ZZ$}` and a positive leading coefficient.
pub fn to_primitive(a: &QPoly) -> (Rational, ZPoly) {
    let denominator = a.iter().fold(Natural::ONE, |acc, c| {
        let d = c.denominator_ref();
        let g = (&acc).gcd(d);
        acc * d / g
    });
    let scaled: ZPoly = a
        .iter()
        .map(|c| Integer::try_from(c * Rational::from(&denominator)).expect("Denominators cleared"))
        .collect();
    let primitive = primitive_part(&scaled);
    let c = a.last().map_or(Rational::ONE, |lc| {
        lc / Rational::from(primitive.last().expect("Non zero").clone())
    });
    (c, primitive)
}

/// Convert an integer polynomial to a rational one.
pub fn to_q(a: &ZPoly) -> QPoly {
    a.iter().map(Rational::from).collect()
}

/// Bézout coefficients for pairwise coprime `a_i`: returns `s_i` with `{$sum_i s_i product_(j != i) a_j = 1$}` and `{$deg s_i < deg a_i$}`.
pub fn multi_bezout(a: &[QPoly]) -> Vec<QPoly> {
    match a {
        [] => vec![],
        [_] => vec![vec![Rational::ONE]],
        [first, rest @ ..] => {
            let product = rest
                .iter()
                .fold(vec![Rational::ONE], |acc, x| qmul(&acc, x));
            // u * first + v * product = 1
            let (_, u, v) = qext_gcd(first, &product);
            let mut res = vec![v];
            for (s, x) in multi_bezout(rest).iter().zip(rest) {
                res.push(qdiv_rem(&qmul(&u, s), x).1);
            }
            res
        }
    }
}

// ---------------------------------------------------------------------------
// Zassenhaus
// ---------------------------------------------------------------------------

/// Lift `f ≡ lc(f) * g0 * h0 mod p`, with `g0`, `h0` monic and coprime, to `f ≡ g * h mod p^k` where `lc(g) = lc(f)` and `h` is monic.
fn hensel_pair(f: &ZPoly, g0: &ModPoly, h0: &ModPoly, p: u64, k: u32) -> (ZPoly, ZPoly) {
    let lc = f.last().expect("Non zero polynomial");
    let g0 = modular::scale(g0, modular::from_integers(&[lc.clone()], p)[0], p);
    let (_, s, t) = modular::ext_gcd(&g0, h0, p);

    let mut g = from_mod(&g0);
    *g.last_mut().expect("Non zero polynomial") = lc.clone();
    let mut h = from_mod(h0);
    let p_int = Integer::from(p);
    let mut m = p_int.clone();
    for _ in 1..k {
        let error: ZPoly = zsub(f, &zmul(&g, &h)).iter().map(|c| c / &m).collect();
        let error = modular::from_integers(&error, p);
        // sigma * g0 + tau * h0 = error, with deg sigma < deg h0 and deg tau < deg g0
        let (q, sigma) = modular::div_rem(&modular::mul(&s, &error, p), h0, p);
        let tau = modular::add(&modular::mul(&t, &error, p), &modular::mul(&q, &g0, p), p);
        g = zadd(&g, &zscale(&from_mod(&tau), &m));
        h = zadd(&h, &zscale(&from_mod(&sigma), &m));
        m *= &p_int;
        // Reduce coefficients, except leading ones which are exact
        let (dg, dh) = (g.len() - 1, h.len() - 1);
        for c in &mut g[..dg] {
            *c = smod(c, &m);
        }
        for c in &mut h[..dh] {
            *c = smod(c, &m);
        }
    }
    (g, h)
}

/// Lift the monic factorization `f ≡ lc(f) * product(factors) mod p` to monic factors modulo `p^k`.
fn hensel_multi(f: &ZPoly, factors: &[ModPoly], p: u64, k: u32, m: &Integer) -> Vec<ZPoly> {
    if let [_] = factors {
        let inv = inv_mod(f.last().expect("Non zero polynomial"), m);
        return vec![smod_poly(&zscale(f, &inv), m)];
    }
    let (left, right) = factors.split_at(factors.len() / 2);
    let product = |factors: &[ModPoly]| {
        factors
            .iter()
            .fold(vec![1], |acc, x| modular::mul(&acc, x, p))
    };
    let (g, h) = hensel_pair(f, &product(left), &product(right), p, k);
    let mut res = hensel_multi(&g, left, p, k, m);
    res.extend(hensel_multi(&h, right, p, k, m));
    res
}

const fn is_prime(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    let mut d = 2;
    while d * d <= n {
        if n % d == 0 {
            return false;
        }
        d += 1;
    }
    true
}

/// Number of good primes tried, the one giving the fewest modular factors is kept.
const PRIME_TRIES: usize = 5;

/// Advance `indices` to the next combination of its size among `0..n`, in lexicographic order.
fn next_combination(indices: &mut [usize], n: usize) -> bool {
    let k = indices.len();
    for i in (0..k).rev() {
        if indices[i] < n - k + i {
            indices[i] += 1;
            for j in i + 1..k {
                indices[j] = indices[j - 1] + 1;
            }
            return true;
        }
    }
    false
}

/// Factor a primitive square-free polynomial with a positive leading coefficient into irreducible factors over `{$ZZ$}`.
///
/// Factors are primitive, with positive leading coefficients.
pub fn zassenhaus(f: &ZPoly) -> Vec<ZPoly> {
    let n = f.len().saturating_sub(1);
    if n <= 1 {
        return vec![f.clone()];
    }
    let lc = f[n].clone();
    let mut rng = Rng::new();

    // Choose the prime giving the fewest modular factors
    let mut best: Option<(u64, Vec<ModPoly>)> = None;
    let mut tries = 0;
    for p in (3..).step_by(2).filter(|p| is_prime(*p)) {
        if (&lc).divisible_by(Integer::from(p)) {
            continue;
        }
        let fp = modular::from_integers(f, p);
        if modular::degree(&modular::gcd(&fp, &modular::derivative(&fp, p), p)) != Some(0) {
            continue;
        }
        let factors = modular::factor(&modular::monic(&fp, p), p, &mut rng);
        if factors.len() == 1 {
            return vec![f.clone()];
        }
        if best.as_ref().is_none_or(|(_, b)| factors.len() < b.len()) {
            best = Some((p, factors));
        }
        tries += 1;
        if tries == PRIME_TRIES {
            break;
        }
    }
    let (p, factors) = best.expect("A good prime exists for square-free polynomials");

    // Bound on the coefficients of factors (Mignotte), lifted factors must determine them
    let max = f
        .iter()
        .map(UnsignedAbs::unsigned_abs)
        .max()
        .expect("Non zero");
    let bound = Integer::from(Natural::from(2u32).pow(n as u64) * Natural::from(n + 1) * max)
        * Integer::from(lc.unsigned_abs());
    let p_int = Integer::from(p);
    let (mut k, mut m) = (1, p_int.clone());
    while m <= Integer::from(2u32) * &bound {
        m *= &p_int;
        k += 1;
    }
    let mut lifted = hensel_multi(f, &factors, p, k, &m);

    // Recombine lifted factors, trying the smallest subsets first
    let mut f = f.clone();
    let mut res = vec![];
    let mut size = 1;
    'sizes: while 2 * size <= lifted.len() {
        let mut subset: Vec<usize> = (0..size).collect();
        loop {
            let lc = f.last().expect("Non zero").clone();
            let candidate = subset.iter().fold(vec![lc.clone()], |acc, i| {
                smod_poly(&zmul(&acc, &lifted[*i]), &m)
            });
            // The constant term of a factor divides the constant term of `lc * f`
            let plausible =
                f[0] == 0u32 || (candidate[0] != 0u32 && (&lc * &f[0]).divisible_by(&candidate[0]));
            if plausible {
                let candidate = primitive_part(&candidate);
                if let Some(quotient) = exact_div(&f, &candidate) {
                    res.push(candidate);
                    f = quotient;
                    for i in subset.iter().rev() {
                        lifted.remove(*i);
                    }
                    continue 'sizes;
                }
            }
            if !next_combination(&mut subset, lifted.len()) {
                break;
            }
        }
        size += 1;
    }
    if f.len() > 1 {
        res.push(f);
    }
    res
}
