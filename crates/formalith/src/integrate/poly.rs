//! Conversions between expressions and dense polynomials with rational or Gaussian rational coefficients.

use malachite::Rational;

pub(crate) use crate::polynom::dense::{Coefficient, Poly};
use crate::{
    context::Symbol,
    field::{
        Ring,
        complex::C,
        real::{R, Real, expr::Expr},
    },
    term::{Expand, SymbolTerm, Term, Value},
};

/// The coefficients of polynomials converted to expressions of a set, its elements.
pub(crate) trait TermCoefficient: Coefficient {
    /// The set whose elements are the coefficients.
    type Set: Ring<Element = Self, ExponantSet = Self::Set, ProductCoefficientSet = Self::Set>;

    /// The set of expressions.
    fn set() -> Self::Set;

    /// The coefficient as a natural number, if it is one.
    fn to_natural(&self) -> Option<usize>;

    /// The factorization of an expression, over `{$QQ$}` or `{$QQ(i)$}`.
    fn factor_term(term: &Term<Self::Set>) -> Term<Self::Set>;
}

impl TermCoefficient for Rational {
    type Set = Real;

    fn set() -> Real {
        R
    }

    fn to_natural(&self) -> Option<usize> {
        usize::try_from(self).ok()
    }

    fn factor_term(term: &Term<Real>) -> Term<Real> {
        term.factor()
    }
}

impl TermCoefficient for [Rational; 2] {
    type Set = C<Real>;

    fn set() -> C<Real> {
        C
    }

    fn to_natural(&self) -> Option<usize> {
        if self[1] == 0 {
            self[0].to_natural()
        } else {
            None
        }
    }

    fn factor_term(term: &Term<C<Real>>) -> Term<C<Real>> {
        term.factor()
    }
}

impl<F: TermCoefficient> Poly<F> {
    /// The polynomial as an expression in `x`.
    pub(crate) fn to_term(&self, x: Symbol) -> Term<F::Set> {
        let set = F::set();
        let x = Term::Symbol(SymbolTerm::new(x, set));
        self.coefficients()
            .iter()
            .enumerate()
            .rev()
            .fold(Term::zero(set), |res, (i, c)| {
                let power = Term::Value(Value::new(F::from_rational(Rational::from(i)), set));
                res + Term::Value(Value::new(c.clone(), set)) * x.pow(&power)
            })
    }

    /// The polynomial in `x` given by an expression, if its coefficients are elements of `F`.
    pub(crate) fn from_term_over(term: &Term<F::Set>, x: Symbol) -> Option<Self> {
        Self::from_expanded(&term.expand(), x)
    }

    fn from_expanded(term: &Term<F::Set>, x: Symbol) -> Option<Self> {
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
                    let n = n.value.to_natural()?;
                    Some(Self::from_expanded(&pow.base, x)?.pow(n))
                }
                _ => None,
            },
            Term::Symbol(_) | Term::Fun(_) => None,
        }
    }
}

impl Poly<Rational> {
    /// The polynomial in `x` given by an expression, if its coefficients are rational numbers.
    pub(crate) fn from_term(term: &Expr, x: Symbol) -> Option<Self> {
        Self::from_term_over(term, x)
    }
}

/// The rational function `{$f = p / q$}` in `x` given by an expression, `q` monic, if its coefficients are
/// rational numbers.
pub(super) fn rational_function(f: &Expr, x: Symbol) -> Option<(Poly, Poly)> {
    rational_function_over(f, x)
}

/// The rational function `{$f = p / q$}` in `x` given by an expression, `q` monic, if its coefficients are
/// elements of `F`.
pub(super) fn rational_function_over<F: TermCoefficient>(
    f: &Term<F::Set>,
    x: Symbol,
) -> Option<(Poly<F>, Poly<F>)> {
    let (num, den) = f.as_fraction(true);
    let num = Poly::<F>::from_term_over(&num, x)?;
    let den = Poly::<F>::from_term_over(&den, x)?;
    if den.is_zero() {
        return None;
    }
    let lead = den.leading().inverse();
    Some((num.scale(&lead), den.scale(&lead)))
}
