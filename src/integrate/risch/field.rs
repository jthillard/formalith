//! Elements of a tower of transcendental extensions `{$K_n = QQ(t_1, ..., t_n)$}` with `{$t_1 = x$}`.
//!
//! An element of level `{$k >= 1$}` is a reduced fraction of polynomials in `{$t_k$}` with coefficients in
//! `{$K_(k - 1)$}`, its denominator monic, and it is always represented at its lowest level, so equal elements
//! have equal representations.

use std::rc::Rc;

use malachite::{
    Rational,
    base::num::basic::traits::{One, Zero},
};

use crate::polynom::dense::{Coefficient, Poly};

/// An element of `{$K_n$}`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Elem {
    /// An element of `{$QQ$}`, the level 0.
    Rational(Rational),
    /// A fraction of a level at least 1.
    Fraction(Rc<Fraction>),
}

/// `{$p(t_k) / q(t_k)$}` with `p` and `q` coprime, `q` monic, coefficients of lower levels, and `p` or `q` not
/// constant.
#[derive(Debug, PartialEq, Eq)]
pub(super) struct Fraction {
    level: usize,
    num: Poly<Elem>,
    den: Poly<Elem>,
}

/// A polynomial in some `{$t_k$}` with coefficients in `{$K_(k - 1)$}`.
pub(super) type EPoly = Poly<Elem>;

impl Elem {
    /// The generator `{$t_k$}` of level `{$k >= 1$}`.
    pub(super) fn generator(level: usize) -> Self {
        Self::from_reduced(level, EPoly::x(), EPoly::one())
    }

    pub(super) fn rational(r: Rational) -> Self {
        Self::Rational(r)
    }

    pub(super) fn integer(n: i64) -> Self {
        Self::Rational(Rational::from(n))
    }

    /// The level of the element, the least `k` with the element in `{$K_k$}`.
    pub(super) fn level(&self) -> usize {
        match self {
            Self::Rational(_) => 0,
            Self::Fraction(f) => f.level,
        }
    }

    /// The rational number, if the element is one.
    pub(super) const fn as_rational(&self) -> Option<&Rational> {
        match self {
            Self::Rational(r) => Some(r),
            Self::Fraction(_) => None,
        }
    }

    /// The element as a fraction `{$p(t_k) / q(t_k)$}` of level `{$k >= 1$}`, with `q` monic.
    pub(super) fn fraction(&self, level: usize) -> (EPoly, EPoly) {
        match self {
            Self::Fraction(f) if f.level == level => (f.num.clone(), f.den.clone()),
            _ => {
                debug_assert!(self.level() < level, "Element of a level above {level}");
                (EPoly::constant(self.clone()), EPoly::one())
            }
        }
    }

    /// The element `{$p / q$}` of level `level`, the polynomials being coprime.
    pub(super) fn from_reduced(level: usize, num: EPoly, den: EPoly) -> Self {
        assert!(!den.is_zero(), "Division by zero");
        let lead = den.leading().inverse();
        let (num, den) = (num.scale(&lead), den.scale(&lead));
        if den.is_constant() && num.is_constant() {
            return num.coefficient(0);
        }
        Self::Fraction(Rc::new(Fraction { level, num, den }))
    }

    /// The element `{$p / q$}` of level `level`.
    pub(super) fn from_fraction(level: usize, num: &EPoly, den: &EPoly) -> Self {
        let g = num.gcd(den);
        if g.degree() == 0 {
            return Self::from_reduced(level, num.clone(), den.clone());
        }
        Self::from_reduced(level, num.exact_div(&g), den.exact_div(&g))
    }

    /// The polynomial `p` of level `level` as an element.
    pub(super) fn from_poly(level: usize, p: EPoly) -> Self {
        Self::from_reduced(level, p, EPoly::one())
    }

    /// `{$e^n$}` for an integer `n`.
    pub(super) fn pow(&self, n: i64) -> Self {
        let base = if n < 0 { self.inverse() } else { self.clone() };
        (0..n.unsigned_abs()).fold(Self::one(), |res, _| res.times(&base))
    }

    /// The value at the point giving the values of `{$t_1, t_2, ...$}`, `None` when a denominator vanishes.
    pub(super) fn eval(&self, point: &[Rational]) -> Option<Rational> {
        match self {
            Self::Rational(r) => Some(r.clone()),
            Self::Fraction(f) => {
                let t = &point[f.level - 1];
                let eval = |p: &EPoly| {
                    p.coefficients()
                        .iter()
                        .rev()
                        .try_fold(Rational::ZERO, |res, c| Some(res * t + c.eval(point)?))
                };
                let den = eval(&f.den)?;
                (den != 0)
                    .then(|| eval(&f.num).map(|num| num / den))
                    .flatten()
            }
        }
    }
}

impl Coefficient for Elem {
    fn from_rational(r: Rational) -> Self {
        Self::Rational(r)
    }

    fn is_zero(&self) -> bool {
        matches!(self, Self::Rational(r) if *r == Rational::ZERO)
    }

    fn plus(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Rational(a), Self::Rational(b)) => Self::Rational(a + b),
            _ if self.is_zero() => other.clone(),
            _ if other.is_zero() => self.clone(),
            _ => {
                let level = self.level().max(other.level());
                let (na, da) = self.fraction(level);
                let (nb, db) = other.fraction(level);
                if da == db {
                    Self::from_fraction(level, &na.add(&nb), &da)
                } else if db.degree() == 0 {
                    Self::from_reduced(level, na.add(&nb.mul(&da)), da)
                } else if da.degree() == 0 {
                    Self::from_reduced(level, nb.add(&na.mul(&db)), db)
                } else {
                    Self::from_fraction(level, &na.mul(&db).add(&nb.mul(&da)), &da.mul(&db))
                }
            }
        }
    }

    fn negate(&self) -> Self {
        match self {
            Self::Rational(r) => Self::Rational(-r),
            Self::Fraction(f) => Self::Fraction(Rc::new(Fraction {
                level: f.level,
                num: f.num.neg(),
                den: f.den.clone(),
            })),
        }
    }

    fn times(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Rational(a), Self::Rational(b)) => Self::Rational(a * b),
            _ if self.is_zero() || other.is_zero() => Self::zero(),
            _ if self.is_one() => other.clone(),
            _ if other.is_one() => self.clone(),
            _ => {
                let level = self.level().max(other.level());
                let (na, da) = self.fraction(level);
                let (nb, db) = other.fraction(level);
                if other.level() < level {
                    Self::from_reduced(level, na.scale(other), da)
                } else if self.level() < level {
                    Self::from_reduced(level, nb.scale(self), db)
                } else {
                    let (g1, g2) = (na.gcd(&db), nb.gcd(&da));
                    Self::from_reduced(
                        level,
                        na.exact_div(&g1).mul(&nb.exact_div(&g2)),
                        da.exact_div(&g2).mul(&db.exact_div(&g1)),
                    )
                }
            }
        }
    }

    fn inverse(&self) -> Self {
        match self {
            Self::Rational(r) => Self::Rational(Rational::ONE / r),
            Self::Fraction(f) => Self::from_reduced(f.level, f.den.clone(), f.num.clone()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_forms() {
        let x = Elem::generator(1);
        let t = Elem::generator(2);
        let one = Elem::one();
        // `{$(x + 1) / x - 1 / x = 1$}`
        let a = x.plus(&one).divide(&x).minus(&one.divide(&x));
        assert_eq!(a, one);
        // `{$t x / x = t$}`, `{$(t + x)^2 / (t + x) = t + x$}`
        assert_eq!(t.times(&x).divide(&x), t);
        let s = t.plus(&x);
        assert_eq!(s.times(&s).divide(&s), s);
        assert_eq!(s.minus(&t), x);
        assert_eq!(
            s.eval(&[Rational::from(2), Rational::from(3)]),
            Some(Rational::from(5))
        );
    }
}
