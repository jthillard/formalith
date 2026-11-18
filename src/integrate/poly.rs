//! Dense univariate polynomials over a field, with rational coefficients for the integration of rational
//! functions, or with coefficients in a differential field for the Risch algorithm.

use std::fmt::Debug;

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

/// The elements of a field of characteristic 0, the coefficients of a [`Poly`].
pub(super) trait Coefficient: Clone + PartialEq + Debug {
    /// The rational number `r` as an element of the field.
    fn from_rational(r: Rational) -> Self;
    fn is_zero(&self) -> bool;
    fn plus(&self, other: &Self) -> Self;
    fn negate(&self) -> Self;
    fn times(&self, other: &Self) -> Self;
    /// The inverse of a non-zero element.
    fn inverse(&self) -> Self;

    fn zero() -> Self {
        Self::from_rational(Rational::ZERO)
    }

    fn one() -> Self {
        Self::from_rational(Rational::ONE)
    }

    fn minus(&self, other: &Self) -> Self {
        self.plus(&other.negate())
    }

    fn divide(&self, other: &Self) -> Self {
        self.times(&other.inverse())
    }

    fn is_one(&self) -> bool {
        *self == Self::one()
    }
}

impl Coefficient for Rational {
    fn from_rational(r: Rational) -> Self {
        r
    }

    fn is_zero(&self) -> bool {
        *self == Self::ZERO
    }

    fn plus(&self, other: &Self) -> Self {
        self + other
    }

    fn negate(&self) -> Self {
        -self
    }

    fn times(&self, other: &Self) -> Self {
        self * other
    }

    fn inverse(&self) -> Self {
        Self::ONE / self
    }
}

/// A polynomial `{$sum_i c_i x^i$}`, its coefficients by increasing degree, without trailing zeros.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Poly<F = Rational>(Vec<F>);

impl<F: Coefficient> Poly<F> {
    /// The polynomial with the given coefficients, by increasing degree.
    pub(super) fn new(mut coefficients: Vec<F>) -> Self {
        while coefficients.last().is_some_and(F::is_zero) {
            coefficients.pop();
        }
        Self(coefficients)
    }

    pub(super) const fn zero() -> Self {
        Self(Vec::new())
    }

    pub(super) fn constant(c: F) -> Self {
        Self::new(vec![c])
    }

    pub(super) fn one() -> Self {
        Self::constant(F::one())
    }

    /// The polynomial `x`.
    pub(super) fn x() -> Self {
        Self(vec![F::zero(), F::one()])
    }

    /// The monomial `{$c x^n$}`.
    pub(super) fn monomial(c: F, n: usize) -> Self {
        let mut coefficients = vec![F::zero(); n];
        coefficients.push(c);
        Self::new(coefficients)
    }

    pub(super) fn coefficients(&self) -> &[F] {
        &self.0
    }

    /// The coefficient of `{$x^i$}`.
    pub(super) fn coefficient(&self, i: usize) -> F {
        self.0.get(i).cloned().unwrap_or_else(F::zero)
    }

    pub(super) const fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    /// Whether the polynomial is a constant, possibly 0.
    pub(super) const fn is_constant(&self) -> bool {
        self.0.len() <= 1
    }

    /// The degree, 0 for the zero polynomial.
    pub(super) const fn degree(&self) -> usize {
        self.0.len().saturating_sub(1)
    }

    /// The leading coefficient, 0 for the zero polynomial.
    pub(super) fn leading(&self) -> F {
        self.0.last().cloned().unwrap_or_else(F::zero)
    }

    /// The largest `n` such that `{$x^n$}` divides the non-zero polynomial.
    pub(super) fn order_at_zero(&self) -> usize {
        self.0.iter().take_while(|c| c.is_zero()).count()
    }

    /// The polynomial divided by `{$x^n$}`, dropping the terms of lower degree.
    pub(super) fn shift_down(&self, n: usize) -> Self {
        Self::new(self.0.iter().skip(n).cloned().collect())
    }

    pub(super) fn scale(&self, c: &F) -> Self {
        Self::new(self.0.iter().map(|a| a.times(c)).collect())
    }

    pub(super) fn add(&self, other: &Self) -> Self {
        let n = self.0.len().max(other.0.len());
        Self::new(
            (0..n)
                .map(|i| self.coefficient(i).plus(&other.coefficient(i)))
                .collect(),
        )
    }

    pub(super) fn neg(&self) -> Self {
        Self(self.0.iter().map(F::negate).collect())
    }

    pub(super) fn sub(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }

    pub(super) fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        let mut res = vec![F::zero(); self.0.len() + other.0.len() - 1];
        for (i, a) in self.0.iter().enumerate() {
            if a.is_zero() {
                continue;
            }
            for (j, b) in other.0.iter().enumerate() {
                res[i + j] = res[i + j].plus(&a.times(b));
            }
        }
        Self::new(res)
    }

    pub(super) fn pow(&self, n: usize) -> Self {
        (0..n).fold(Self::one(), |res, _| res.mul(self))
    }

    /// The derivative with respect to the variable.
    pub(super) fn derivative(&self) -> Self {
        Self::new(
            self.0
                .iter()
                .enumerate()
                .skip(1)
                .map(|(i, c)| c.times(&F::from_rational(Rational::from(i))))
                .collect(),
        )
    }

    /// The value at `x`.
    pub(super) fn eval(&self, x: &F) -> F {
        self.0
            .iter()
            .rev()
            .fold(F::zero(), |res, c| res.times(x).plus(c))
    }

    /// Quotient and remainder of the euclidean division by a non-zero `divisor`.
    pub(super) fn div_rem(&self, divisor: &Self) -> (Self, Self) {
        assert!(!divisor.is_zero(), "Division by the zero polynomial");
        let mut rem = self.0.clone();
        let d = divisor.degree();
        let lead = divisor.leading().inverse();
        if rem.len() <= d {
            return (Self::zero(), self.clone());
        }
        let mut quo = vec![F::zero(); rem.len() - d];
        for i in (0..quo.len()).rev() {
            let c = rem[i + d].times(&lead);
            if !c.is_zero() {
                for (j, b) in divisor.0.iter().enumerate() {
                    rem[i + j] = rem[i + j].minus(&c.times(b));
                }
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

    /// Whether `divisor` divides the polynomial.
    pub(super) fn divisible_by(&self, divisor: &Self) -> bool {
        self.rem(divisor).is_zero()
    }

    /// The polynomial divided by its leading coefficient.
    pub(super) fn monic(&self) -> Self {
        if self.is_zero() {
            return Self::zero();
        }
        self.scale(&self.leading().inverse())
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
        let lead = r0.leading().inverse();
        (s0.scale(&lead), t0.scale(&lead), r0.scale(&lead))
    }

    /// The monic gcd.
    pub(super) fn gcd(&self, other: &Self) -> Self {
        let (mut a, mut b) = (self.clone(), other.clone());
        while !b.is_zero() {
            (a, b) = (b.clone(), a.rem(&b));
        }
        a.monic()
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

    /// The resultant of `self` and `other`, computed with euclidean divisions.
    pub(super) fn resultant(&self, other: &Self) -> F {
        if self.is_zero() || other.is_zero() {
            return F::zero();
        }
        let (m, n) = (self.degree(), other.degree());
        if n == 0 {
            return power(&other.leading(), m);
        }
        if m == 0 {
            return power(&self.leading(), n);
        }
        let sign = |res: F| {
            if m % 2 == 1 && n % 2 == 1 {
                res.negate()
            } else {
                res
            }
        };
        if m < n {
            return sign(other.resultant(self));
        }
        // `{$res(f, g) = (-1)^(m n) res(g, f) = (-1)^(m n) lc(g)^(m - deg r) res(g, r)$}` with `{$r = f mod g$}`
        let r = self.rem(other);
        if r.is_zero() {
            return F::zero();
        }
        sign(power(&other.leading(), m - r.degree()).times(&other.resultant(&r)))
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

    /// The polynomial with the coefficients mapped by `f`.
    pub(super) fn map<G: Coefficient>(&self, f: impl Fn(&F) -> G) -> Poly<G> {
        Poly::new(self.0.iter().map(f).collect())
    }
}

/// `{$c^n$}`.
fn power<F: Coefficient>(c: &F, n: usize) -> F {
    (0..n).fold(F::one(), |res, _| res.times(c))
}

impl Poly<Rational> {
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
            Term::Add(add) => add.iter().try_fold(Self::zero(), |res, t| {
                Some(res.add(&Self::from_expanded(t, x)?))
            }),
            Term::Mul(mul) => mul
                .iter()
                .try_fold(Self::constant(mul.coefficient.clone()), |res, t| {
                    Some(res.mul(&Self::from_expanded(t, x)?))
                }),
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
