//! Conversions between expressions and dense polynomials with rational coefficients.

use crate::field::real::expr::{Expr, value, variable, zero};
use malachite::{Rational, base::num::basic::traits::One};

pub(crate) use crate::polynom::dense::{Coefficient, Poly};
use crate::{
    context::Symbol,
    term::{Expand, Term},
};

impl Poly<Rational> {
    /// The polynomial as an expression in `x`.
    pub(crate) fn to_term(&self, x: Symbol) -> Expr {
        let x = variable(x);
        self.coefficients()
            .iter()
            .enumerate()
            .rev()
            .fold(zero(), |res, (i, c)| {
                res + value(c.clone()) * x.pow(&value(Rational::from(i)))
            })
    }

    /// The polynomial in `x` given by an expression, if its coefficients are rational numbers.
    pub(crate) fn from_term(term: &Expr, x: Symbol) -> Option<Self> {
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
