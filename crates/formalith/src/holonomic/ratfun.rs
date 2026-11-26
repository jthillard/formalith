//! Rational functions `{$p(t) / q(t)$}` in one variable with coefficients in `{$QQ(t_1, ..., t_n)$}`, the
//! coefficients of differential and recurrence operators.

use malachite::Rational;

use crate::{
    integrate::rational::rational_roots,
    polynom::{
        dense::{Coefficient, Poly},
        fraction::{EPoly, Elem, sample_points},
    },
    sum::field::reduce,
};

/// Largest natural root looked for in a polynomial whose coefficients have parameters.
const MAX_ROOT: u64 = 10_000;

/// A reduced fraction `{$p / q$}` with `q` monic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RatFun {
    pub(crate) num: EPoly,
    pub(crate) den: EPoly,
}

impl RatFun {
    /// The fraction `{$p / q$}`, reduced.
    pub(crate) fn new(num: &EPoly, den: &EPoly) -> Self {
        let (num, den) = reduce(num, den);
        Self { num, den }
    }

    /// The polynomial `p`.
    pub(crate) fn poly(p: EPoly) -> Self {
        Self {
            num: p,
            den: EPoly::one(),
        }
    }

    /// The constant `c`.
    pub(crate) fn constant(c: Elem) -> Self {
        Self::poly(EPoly::constant(c))
    }

    /// The derivative with respect to `t`.
    pub(crate) fn derivative(&self) -> Self {
        let num = self
            .num
            .derivative()
            .mul(&self.den)
            .sub(&self.num.mul(&self.den.derivative()));
        Self::new(&num, &self.den.mul(&self.den))
    }

    /// `{$f(t + 1)$}`.
    pub(crate) fn shifted(&self) -> Self {
        self.shifted_by(1)
    }

    /// `{$f(t + k)$}`.
    pub(crate) fn shifted_by(&self, k: i64) -> Self {
        let k = Elem::integer(k);
        Self::new(&self.num.shift(&k), &self.den.shift(&k))
    }

    /// The value at `t`, `None` at a pole.
    pub(crate) fn eval(&self, t: &Elem) -> Option<Elem> {
        let den = self.den.eval(t);
        (!den.is_zero()).then(|| self.num.eval(t).divide(&den))
    }
}

impl Coefficient for RatFun {
    fn from_rational(r: Rational) -> Self {
        Self::constant(Elem::rational(r))
    }

    fn is_zero(&self) -> bool {
        self.num.is_zero()
    }

    fn plus(&self, other: &Self) -> Self {
        if self.is_zero() {
            return other.clone();
        }
        if other.is_zero() {
            return self.clone();
        }
        if self.den == other.den {
            return Self::new(&self.num.add(&other.num), &self.den);
        }
        let num = self.num.mul(&other.den).add(&other.num.mul(&self.den));
        Self::new(&num, &self.den.mul(&other.den))
    }

    fn negate(&self) -> Self {
        Self {
            num: self.num.neg(),
            den: self.den.clone(),
        }
    }

    fn times(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        Self::new(&self.num.mul(&other.num), &self.den.mul(&other.den))
    }

    fn inverse(&self) -> Self {
        Self::new(&self.den, &self.num)
    }
}

/// The natural numbers `n` with `{$p(n) = 0$}`, `None` when they can't be bounded. With parameters in the
/// coefficients, the roots of `p` at a sample point of the parameters are candidates checked exactly.
pub fn natural_roots(p: &EPoly) -> Option<Vec<u64>> {
    if p.is_zero() {
        return None;
    }
    if let Some(p) = p.to_rational() {
        let (roots, _) = rational_roots(&p, crate::context::Symbol::new("@n"));
        return Some(
            roots
                .into_iter()
                .filter_map(|r| u64::try_from(&r).ok())
                .collect(),
        );
    }
    let levels = p.coefficients().iter().map(Elem::level).max().unwrap_or(0);
    let point = sample_points(levels)
        .take(20)
        .find(|point| p.leading().eval(point).is_some_and(|v| v != 0))?;
    let specialized = p
        .coefficients()
        .iter()
        .map(|c| c.eval(&point))
        .collect::<Option<Vec<_>>>()?;
    let (candidates, _) =
        rational_roots(&Poly::new(specialized), crate::context::Symbol::new("@n"));
    Some(
        candidates
            .into_iter()
            .filter_map(|r| u64::try_from(&r).ok())
            .filter(|&n| n <= MAX_ROOT)
            .filter(|&n| p.eval(&Elem::integer(n.cast_signed())).is_zero())
            .collect(),
    )
}
