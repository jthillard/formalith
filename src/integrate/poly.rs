//! Dense univariate polynomials with rational coefficients, used by the integration of rational functions.

use malachite::{
    Rational,
    base::num::basic::traits::{One, Zero},
};

use crate::{
    context::Symbol,
    limit::{value, variable},
    term::{Expand, Term},
};

use super::Expr;

/// A polynomial `{$sum_i c_i x^i$}`, its coefficients by increasing degree, without trailing zeros.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Poly(Vec<Rational>);

impl Poly {
    /// The polynomial with the given coefficients, by increasing degree.
    pub(super) fn new(mut coefficients: Vec<Rational>) -> Self {
        while coefficients.last() == Some(&Rational::ZERO) {
            coefficients.pop();
        }
        Self(coefficients)
    }

    pub(super) const fn zero() -> Self {
        Self(Vec::new())
    }

    pub(super) fn constant(c: Rational) -> Self {
        Self::new(vec![c])
    }

    pub(super) fn one() -> Self {
        Self::constant(Rational::ONE)
    }

    /// The polynomial `x`.
    pub(super) fn x() -> Self {
        Self(vec![Rational::ZERO, Rational::ONE])
    }

    pub(super) fn coefficients(&self) -> &[Rational] {
        &self.0
    }

    pub(super) const fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    /// The degree, 0 for the zero polynomial.
    pub(super) const fn degree(&self) -> usize {
        self.0.len().saturating_sub(1)
    }

    /// The leading coefficient, 0 for the zero polynomial.
    pub(super) fn leading(&self) -> Rational {
        self.0.last().cloned().unwrap_or(Rational::ZERO)
    }

    pub(super) fn scale(&self, c: &Rational) -> Self {
        Self::new(self.0.iter().map(|a| a * c).collect())
    }

    pub(super) fn add(&self, other: &Self) -> Self {
        let n = self.0.len().max(other.0.len());
        Self::new(
            (0..n)
                .map(|i| {
                    self.0.get(i).cloned().unwrap_or(Rational::ZERO)
                        + other.0.get(i).cloned().unwrap_or(Rational::ZERO)
                })
                .collect(),
        )
    }

    pub(super) fn sub(&self, other: &Self) -> Self {
        self.add(&other.scale(&-Rational::ONE))
    }

    pub(super) fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        let mut res = vec![Rational::ZERO; self.0.len() + other.0.len() - 1];
        for (i, a) in self.0.iter().enumerate() {
            for (j, b) in other.0.iter().enumerate() {
                res[i + j] += a * b;
            }
        }
        Self::new(res)
    }

    pub(super) fn pow(&self, n: usize) -> Self {
        (0..n).fold(Self::one(), |res, _| res.mul(self))
    }

    pub(super) fn derivative(&self) -> Self {
        Self::new(
            self.0
                .iter()
                .enumerate()
                .skip(1)
                .map(|(i, c)| c * Rational::from(i))
                .collect(),
        )
    }

    /// The antiderivative vanishing at 0.
    pub(super) fn antiderivative(&self) -> Self {
        let mut res = vec![Rational::ZERO];
        res.extend(
            self.0
                .iter()
                .enumerate()
                .map(|(i, c)| c / Rational::from(i + 1)),
        );
        Self::new(res)
    }

    /// Quotient and remainder of the euclidean division by a non-zero `divisor`.
    pub(super) fn div_rem(&self, divisor: &Self) -> (Self, Self) {
        assert!(!divisor.is_zero(), "Division by the zero polynomial");
        let mut rem = self.0.clone();
        let d = divisor.degree();
        let lead = divisor.leading();
        if rem.len() <= d {
            return (Self::zero(), self.clone());
        }
        let mut quo = vec![Rational::ZERO; rem.len() - d];
        for i in (0..quo.len()).rev() {
            let c = &rem[i + d] / &lead;
            for (j, b) in divisor.0.iter().enumerate() {
                rem[i + j] -= &c * b;
            }
            quo[i] = c;
        }
        rem.truncate(d);
        (Self::new(quo), Self::new(rem))
    }

    pub(super) fn rem(&self, divisor: &Self) -> Self {
        self.div_rem(divisor).1
    }

    /// The exact quotient by `divisor`.
    pub(super) fn exact_div(&self, divisor: &Self) -> Self {
        let (quo, rem) = self.div_rem(divisor);
        debug_assert!(rem.is_zero(), "Inexact polynomial division");
        quo
    }

    /// The polynomial divided by its leading coefficient.
    pub(super) fn monic(&self) -> Self {
        if self.is_zero() {
            return Self::zero();
        }
        self.scale(&(Rational::ONE / self.leading()))
    }

    /// `(s, t, g)` with `{$s a + t b = g$}`, `g` being the monic gcd of `a = self` and `b`.
    pub(super) fn extended_gcd(&self, other: &Self) -> (Self, Self, Self) {
        let (mut r0, mut r1) = (self.clone(), other.clone());
        let (mut s0, mut s1) = (Self::one(), Self::zero());
        let (mut t0, mut t1) = (Self::zero(), Self::one());
        while !r1.is_zero() {
            let (q, r) = r0.div_rem(&r1);
            (r0, r1) = (r1, r);
            let s = s0.sub(&q.mul(&s1));
            (s0, s1) = (s1, s);
            let t = t0.sub(&q.mul(&t1));
            (t0, t1) = (t1, t);
        }
        if r0.is_zero() {
            return (s0, t0, r0);
        }
        let lead = Rational::ONE / r0.leading();
        (s0.scale(&lead), t0.scale(&lead), r0.scale(&lead))
    }

    pub(super) fn gcd(&self, other: &Self) -> Self {
        self.extended_gcd(other).2
    }

    /// `(s, t)` with `{$s a + t b = c$}` and `{$deg s < deg b$}`, for `a = self`, when `{$gcd(a, b)$}` divides `c`.
    pub(super) fn diophantine(&self, b: &Self, c: &Self) -> (Self, Self) {
        let (s, _, g) = self.extended_gcd(b);
        let q = c.exact_div(&g);
        let s = s.mul(&q).rem(b);
        // `{$t = (c - s a) / b$}`
        let t = c.sub(&s.mul(self)).exact_div(b);
        (s, t)
    }

    /// The inverse of `self` modulo `m`, which must be coprime with it.
    pub(super) fn inverse_mod(&self, m: &Self) -> Self {
        self.diophantine(m, &Self::one()).0
    }

    /// The square-free factorization `{$f = c product_i P_i^i$}` (Yun's algorithm): the monic `P_i` by
    /// increasing `i`, possibly constant.
    pub(super) fn square_free(&self) -> Vec<Self> {
        let f = self.monic();
        let df = f.derivative();
        let a = f.gcd(&df);
        let mut b = f.exact_div(&a);
        let mut c = df.exact_div(&a);
        let mut d = c.sub(&b.derivative());
        let mut res = vec![];
        while b.degree() > 0 {
            let a = b.gcd(&d);
            b = b.exact_div(&a);
            c = d.exact_div(&a);
            d = c.sub(&b.derivative());
            res.push(a);
        }
        res
    }

    /// The polynomial as an expression in `x`.
    pub(super) fn to_term(&self, x: Symbol) -> Expr {
        let x = variable(x);
        self.0
            .iter()
            .enumerate()
            .rev()
            .fold(Term::zero(crate::field::real::R), |res, (i, c)| {
                res + value(c.clone()) * x.pow(&value(Rational::from(i)))
            })
    }

    /// The polynomial in `x` given by an expression, if its coefficients are rational numbers.
    pub(super) fn from_term(term: &Expr, x: Symbol) -> Option<Self> {
        Self::from_expanded(&term.expand(), x)
    }

    fn from_expanded(term: &Expr, x: Symbol) -> Option<Self> {
        match term {
            Term::Value(v) => Some(Self::constant(v.value.clone())),
            Term::Symbol(s) if s.symbol == x => Some(Self::x()),
            Term::Add(add) => add
                .iter()
                .try_fold(Self::zero(), |res, t| Some(res.add(&Self::from_expanded(t, x)?))),
            Term::Mul(mul) => mul.iter().try_fold(
                Self::constant(mul.coefficient.clone()),
                |res, t| Some(res.mul(&Self::from_expanded(t, x)?)),
            ),
            Term::Pow(pow) => match &**pow.exponant {
                Term::Value(n) => {
                    let n = usize::try_from(&n.value).ok()?;
                    Some(Self::from_expanded(&pow.base, x)?.pow(n))
                }
                _ => None,
            },
            Term::Symbol(_) | Term::Fun(_) => None,
        }
    }
}

/// The rational function `{$f = p / q$}` in `x` given by an expression, `q` monic, if its coefficients are
/// rational numbers.
pub(super) fn rational_function(f: &Expr, x: Symbol) -> Option<(Poly, Poly)> {
    let (num, den) = f.as_fraction(true);
    let num = Poly::from_term(&num, x)?;
    let den = Poly::from_term(&den, x)?;
    if den.is_zero() {
        return None;
    }
    let lead = Rational::ONE / den.leading();
    Some((num.scale(&lead), den.scale(&lead)))
}
