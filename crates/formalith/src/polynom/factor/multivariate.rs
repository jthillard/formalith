//! Sparse multivariate polynomials over `{$QQ$}`, and Wang's multivariate factorization algorithm (EEZ lifting).

use std::collections::{BTreeMap, btree_map::Entry};

use malachite::{
    Integer, Natural, Rational,
    base::num::{
        arithmetic::traits::{BinomialCoefficient, Pow},
        basic::traits::{One, Zero},
    },
};

use super::{
    modular::Rng,
    univariate::{self, QPoly, ZPoly},
};
use crate::combinatorics::next_combination;

/// A sparse polynomial in `n` variables over `{$QQ$}`, mapping exponent vectors to non-zero coefficients.
///
/// Exponent vectors are compared lexicographically, so the last entry is the leading term for the lex order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SparsePoly {
    n: usize,
    terms: BTreeMap<Vec<u32>, Rational>,
}

impl SparsePoly {
    /// The zero polynomial in `n` variables.
    pub const fn zero(n: usize) -> Self {
        Self {
            n,
            terms: BTreeMap::new(),
        }
    }
    /// The constant polynomial `c` in `n` variables.
    pub fn constant(n: usize, c: Rational) -> Self {
        let mut res = Self::zero(n);
        res.add_term(vec![0; n], c);
        res
    }
    /// Number of variables.
    pub const fn variable_count(&self) -> usize {
        self.n
    }
    /// Iterate over `(exponents, coefficient)` pairs.
    pub fn terms(&self) -> impl Iterator<Item = (&Vec<u32>, &Rational)> {
        self.terms.iter()
    }
    /// Add `c * x^exponents` to the polynomial.
    pub fn add_term(&mut self, exponents: Vec<u32>, c: Rational) {
        debug_assert_eq!(exponents.len(), self.n);
        if c == 0u32 {
            return;
        }
        match self.terms.entry(exponents) {
            Entry::Vacant(entry) => {
                entry.insert(c);
            }
            Entry::Occupied(mut entry) => {
                *entry.get_mut() += c;
                if *entry.get() == 0u32 {
                    entry.remove();
                }
            }
        }
    }
    /// Check if the polynomial is zero.
    pub const fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }
    /// Check if the polynomial is a constant.
    pub fn is_constant(&self) -> bool {
        self.terms.keys().all(|e| e.iter().all(|x| *x == 0))
    }
    /// Leading coefficient for the lex order.
    pub fn leading_coefficient(&self) -> Rational {
        self.terms
            .last_key_value()
            .map_or(Rational::ZERO, |(_, c)| c.clone())
    }
    /// Degree in the variable `var`.
    pub fn degree_in(&self, var: usize) -> u32 {
        self.terms.keys().map(|e| e[var]).max().unwrap_or(0)
    }
    /// Total degree.
    pub fn total_degree(&self) -> u32 {
        self.terms.keys().map(|e| e.iter().sum()).max().unwrap_or(0)
    }

    /// `self + other`
    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        let mut res = self.clone();
        for (e, c) in &other.terms {
            res.add_term(e.clone(), c.clone());
        }
        res
    }
    /// `self - other`
    #[must_use]
    pub fn sub(&self, other: &Self) -> Self {
        let mut res = self.clone();
        for (e, c) in &other.terms {
            res.add_term(e.clone(), -c);
        }
        res
    }
    /// `self * other`
    #[must_use]
    pub fn mul(&self, other: &Self) -> Self {
        let mut res = Self::zero(self.n);
        for (e1, c1) in &self.terms {
            for (e2, c2) in &other.terms {
                let e = e1.iter().zip(e2).map(|(a, b)| a + b).collect();
                res.add_term(e, c1 * c2);
            }
        }
        res
    }
    /// `c * self`
    #[must_use]
    pub fn scale(&self, c: &Rational) -> Self {
        if *c == 0u32 {
            return Self::zero(self.n);
        }
        Self {
            n: self.n,
            terms: self.terms.iter().map(|(e, x)| (e.clone(), x * c)).collect(),
        }
    }
    /// `self^e`
    #[must_use]
    pub fn pow(&self, e: usize) -> Self {
        (0..e).fold(Self::constant(self.n, Rational::ONE), |acc, _| {
            acc.mul(self)
        })
    }
    /// `self * var^d`
    #[must_use]
    pub fn mul_var(&self, var: usize, d: u32) -> Self {
        Self {
            n: self.n,
            terms: self
                .terms
                .iter()
                .map(|(e, c)| {
                    let mut e = e.clone();
                    e[var] += d;
                    (e, c.clone())
                })
                .collect(),
        }
    }
    /// Coefficient of `var^d`, as a polynomial without `var`.
    #[must_use]
    pub fn coefficient_in(&self, var: usize, d: u32) -> Self {
        Self {
            n: self.n,
            terms: self
                .terms
                .iter()
                .filter(|(e, _)| e[var] == d)
                .map(|(e, c)| {
                    let mut e = e.clone();
                    e[var] = 0;
                    (e, c.clone())
                })
                .collect(),
        }
    }
    /// Substitute `var = value`.
    #[must_use]
    pub fn evaluate(&self, var: usize, value: &Integer) -> Self {
        let value = Rational::from(value);
        let mut res = Self::zero(self.n);
        for (e, c) in &self.terms {
            let mut e = e.clone();
            let power = (&value).pow(u64::from(e[var]));
            e[var] = 0;
            res.add_term(e, c * power);
        }
        res
    }
    /// Substitute `var = var + value`.
    #[must_use]
    pub fn shift(&self, var: usize, value: &Integer) -> Self {
        if *value == 0u32 {
            return self.clone();
        }
        let value = Rational::from(value);
        let mut res = Self::zero(self.n);
        for (e, c) in &self.terms {
            let d = e[var];
            for j in 0..=d {
                let mut e = e.clone();
                e[var] = j;
                let binomial = Rational::from(Natural::binomial_coefficient(
                    Natural::from(d),
                    Natural::from(j),
                ));
                res.add_term(e, c * binomial * (&value).pow(u64::from(d - j)));
            }
        }
        res
    }
    /// Convert a polynomial in `var` only to a dense polynomial.
    pub fn to_dense(&self, var: usize) -> QPoly {
        let mut res = vec![Rational::ZERO; self.degree_in(var) as usize + 1];
        for (e, c) in &self.terms {
            debug_assert!(e.iter().enumerate().all(|(i, x)| i == var || *x == 0));
            res[e[var] as usize] += c;
        }
        QPoly::new(res)
    }
    /// Create a polynomial in `n` variables from a dense polynomial in `var`.
    pub fn from_dense(n: usize, var: usize, a: &QPoly) -> Self {
        let mut res = Self::zero(n);
        for (i, c) in a.coefficients().iter().enumerate() {
            let mut e = vec![0; n];
            e[var] = u32::try_from(i).expect("Degree fits in u32");
            res.add_term(e, c.clone());
        }
        res
    }
    /// Keep only variables `vars`, in this order. Other variables must not appear.
    #[must_use]
    pub fn select(&self, vars: &[usize]) -> Self {
        Self {
            n: vars.len(),
            terms: self
                .terms
                .iter()
                .map(|(e, c)| (vars.iter().map(|v| e[*v]).collect(), c.clone()))
                .collect(),
        }
    }
    /// Inverse of [`Self::select`], going back to `n` variables.
    #[must_use]
    pub fn unselect(&self, n: usize, vars: &[usize]) -> Self {
        Self {
            n,
            terms: self
                .terms
                .iter()
                .map(|(e, c)| {
                    let mut res = vec![0; n];
                    for (v, x) in vars.iter().zip(e) {
                        res[*v] = *x;
                    }
                    (res, c.clone())
                })
                .collect(),
        }
    }
    /// Write the polynomial as `c * p`, with `p` having coprime integer coefficients and a positive leading coefficient.
    #[must_use]
    pub fn primitive(&self) -> (Rational, Self) {
        let coefficients: Vec<Rational> = self.terms.values().cloned().collect();
        // `to_primitive` uses the last coefficient for the sign, which is the leading one here
        let (c, _) = univariate::to_primitive(&coefficients);
        (c.clone(), self.scale(&(Rational::ONE / c)))
    }
}

/// Result of [`wang`].
pub enum WangResult {
    /// The polynomial is irreducible.
    Irreducible,
    /// Each polynomial is an irreducible factor times a polynomial without the main variable.
    Factors(Vec<SparsePoly>),
    /// A splitting of the polynomial, up to factors without the main variable, whose parts may still be reducible.
    Split(Vec<SparsePoly>),
}

/// An evaluation point and the factorization of the polynomial evaluated at this point.
struct Image {
    point: Vec<Integer>,
    factors: Vec<ZPoly>,
    tried: bool,
}

/// Number of valid evaluation points compared before lifting.
const POINT_CANDIDATES: usize = 3;
/// Number of evaluation points tried for the lifting of all factors at once.
const LIFT_TRIES: usize = 5;
/// Number of evaluation points drawn before giving up.
const MAX_POINTS: usize = 500;

/// Factor `f`, primitive and square-free in the main variable `0`, using Wang's algorithm.
///
/// Returns `None` if no evaluation point is suitable, which happens when `f` is not square-free.
pub fn wang(f: &SparsePoly) -> Option<WangResult> {
    let n = f.variable_count();
    let degree = f.degree_in(0);
    let lc = f.coefficient_in(0, degree);
    let mut rng = Rng::new();

    let mut images: Vec<Image> = vec![];
    let mut lifted = 0;
    for attempt in 0..MAX_POINTS {
        let Some(image) = image_at(f, &lc, &point(attempt, n, &mut rng)) else {
            continue;
        };
        if image.factors.len() == 1 {
            return Some(WangResult::Irreducible);
        }
        images.push(image);
        if images.len() < POINT_CANDIDATES {
            continue;
        }
        // Extraneous factors at the best point make lifting fail, try other points then
        images.sort_by_key(|image| image.factors.len());
        if let Some(image) = images.iter_mut().find(|image| !image.tried) {
            image.tried = true;
            let factors: Vec<QPoly> = image.factors.iter().map(univariate::to_q).collect();
            if let Some(res) = lift_at(f, &lc, &image.point, &factors) {
                return Some(WangResult::Factors(res));
            }
            lifted += 1;
        }
        if lifted < LIFT_TRIES {
            continue;
        }

        // Some subset of image factors is the image of a true factor, try splittings into two parts
        let image = &images[0];
        let r = image.factors.len();
        for size in 1..=r / 2 {
            let mut subset: Vec<usize> = (0..size).collect();
            loop {
                let product = |inside: bool| {
                    image
                        .factors
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| subset.contains(i) == inside)
                        .fold(QPoly::one(), |acc, (_, x)| acc.mul(&univariate::to_q(x)))
                };
                if let Some(res) = lift_at(f, &lc, &image.point, &[product(true), product(false)]) {
                    return Some(WangResult::Split(res));
                }
                if !next_combination(&mut subset, r) {
                    break;
                }
            }
        }
        return Some(WangResult::Irreducible);
    }
    None
}

/// Deterministic sequence of evaluation points for variables `1..n`, starting at zero and growing.
fn point(attempt: usize, n: usize, rng: &mut Rng) -> Vec<Integer> {
    let range = 2 * (attempt as u64 / 4 + 1) + 1;
    (1..n)
        .map(|_| {
            if attempt == 0 {
                Integer::ZERO
            } else {
                Integer::from(rng.next() % range) - Integer::from(range / 2)
            }
        })
        .collect()
}

fn evaluate_all(f: &SparsePoly, point: &[Integer]) -> SparsePoly {
    point
        .iter()
        .enumerate()
        .fold(f.clone(), |acc, (i, a)| acc.evaluate(i + 1, a))
}

/// Factor `f` evaluated at `point`, if the point keeps the degree and square-freeness of `f`.
fn image_at(f: &SparsePoly, lc: &SparsePoly, point: &[Integer]) -> Option<Image> {
    if evaluate_all(lc, point).is_zero() {
        return None;
    }
    let image = evaluate_all(f, point).to_dense(0);
    if !univariate::is_square_free(&image) {
        return None;
    }
    let (_, primitive) = univariate::to_primitive(image.coefficients());
    Some(Image {
        point: point.to_vec(),
        factors: univariate::zassenhaus(&primitive),
        tried: false,
    })
}

/// Lift the factorization `images` of `f` at `point` to a factorization of `lc^(r-1) * f`, where every factor has `lc` as leading coefficient in the main variable.
fn lift_at(
    f: &SparsePoly,
    lc: &SparsePoly,
    point: &[Integer],
    images: &[QPoly],
) -> Option<Vec<SparsePoly>> {
    let n = f.variable_count();
    // Move the evaluation point to zero
    let shift = |p: &SparsePoly, sign: bool| {
        point.iter().enumerate().fold(p.clone(), |acc, (i, a)| {
            acc.shift(i + 1, &if sign { a.clone() } else { -a })
        })
    };
    let f = shift(f, true);
    let lc = shift(lc, true);
    let lc_image = evaluate_all(&lc, &vec![Integer::ZERO; n - 1]).leading_coefficient();
    let target = lc.pow(images.len() - 1).mul(&f);

    // Every image factor gets the leading coefficient of `f` at the point
    let images: Vec<QPoly> = images
        .iter()
        .map(|u| u.scale(&(&lc_image / u.leading())))
        .collect();
    let bezout = univariate::multi_bezout(&images);
    let degrees: Vec<u32> = (0..n).map(|v| target.degree_in(v)).collect();

    let mut factors: Vec<SparsePoly> = images
        .iter()
        .map(|u| SparsePoly::from_dense(n, 0, u))
        .collect();
    for k in 1..n {
        let restrict =
            |p: &SparsePoly| (k + 1..n).fold(p.clone(), |acc, v| acc.evaluate(v, &Integer::ZERO));
        let target_k = restrict(&target);
        let lc_k = restrict(&lc);
        // Replace leading coefficients
        for (factor, image) in factors.iter_mut().zip(&images) {
            let d = u32::try_from(image.degree()).expect("Degree fits in u32");
            *factor = factor
                .sub(&factor.coefficient_in(0, d).mul_var(0, d))
                .add(&lc_k.mul_var(0, d));
        }
        let base: Vec<SparsePoly> = factors
            .iter()
            .map(|u| u.evaluate(k, &Integer::ZERO))
            .collect();
        let product = |factors: &[SparsePoly]| {
            factors
                .iter()
                .fold(SparsePoly::constant(n, Rational::ONE), |acc, u| acc.mul(u))
        };
        let mut error = target_k.sub(&product(&factors));
        for m in 1..=degrees[k] {
            if error.is_zero() {
                break;
            }
            let c = error.coefficient_in(k, m);
            if c.is_zero() {
                continue;
            }
            let sigma = diophantine(&base, &c, k - 1, &degrees, &images, &bezout);
            for (factor, s) in factors.iter_mut().zip(&sigma) {
                *factor = factor.add(&s.mul_var(k, m));
            }
            error = target_k.sub(&product(&factors));
        }
        if !error.is_zero() {
            return None;
        }
    }
    Some(factors.iter().map(|u| shift(u, false)).collect())
}

/// Solve `{$sum_i sigma_i product_(j != i) a_j = c$}` modulo `{$(x_1, ..., x_v)^(d+1)$}`, where `a_i` only contain variables `0..=v`.
fn diophantine(
    a: &[SparsePoly],
    c: &SparsePoly,
    v: usize,
    degrees: &[u32],
    images: &[QPoly],
    bezout: &[QPoly],
) -> Vec<SparsePoly> {
    let n = c.variable_count();
    if v == 0 {
        // The `a_i` are the univariate images
        let c = c.to_dense(0);
        return images
            .iter()
            .zip(bezout)
            .map(|(a, s)| SparsePoly::from_dense(n, 0, &c.mul(s).rem(a)))
            .collect();
    }
    let others: Vec<SparsePoly> = (0..a.len())
        .map(|i| {
            a.iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .fold(SparsePoly::constant(n, Rational::ONE), |acc, (_, x)| {
                    acc.mul(x)
                })
        })
        .collect();
    let base: Vec<SparsePoly> = a.iter().map(|x| x.evaluate(v, &Integer::ZERO)).collect();
    let combine = |sigma: &[SparsePoly]| {
        sigma
            .iter()
            .zip(&others)
            .fold(c.clone(), |acc, (s, b)| acc.sub(&s.mul(b)))
    };

    let mut sigma = diophantine(
        &base,
        &c.evaluate(v, &Integer::ZERO),
        v - 1,
        degrees,
        images,
        bezout,
    );
    let mut error = combine(&sigma);
    for m in 1..=degrees[v] {
        if error.is_zero() {
            break;
        }
        let cm = error.coefficient_in(v, m);
        if cm.is_zero() {
            continue;
        }
        let delta = diophantine(&base, &cm, v - 1, degrees, images, bezout);
        for (s, d) in sigma.iter_mut().zip(&delta) {
            *s = s.add(&d.mul_var(v, m));
        }
        error = combine(&sigma);
    }
    sigma
}
