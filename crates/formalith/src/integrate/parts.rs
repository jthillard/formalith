//! Integration by parts, `{$integral u v' = u v - integral u' v$}`.

use crate::field::real::expr::{Expr, unary};
use crate::{
    context::{Context, Symbol},
    field::real::R,
    term::{Expand, Mul, Normalize, Term},
};

use super::{Integrator, factors, poly::Poly};

pub(super) fn integrate(integrator: &mut Integrator, f: &Expr, x: Symbol) -> Option<Expr> {
    let factors = factors(f);
    // Logarithms and inverse functions are differentiated, then polynomials
    let u_index = factors.iter().position(is_logarithmic).or_else(|| {
        (factors.len() > 1)
            .then(|| {
                factors
                    .iter()
                    .position(|factor| Poly::from_term(factor, x).is_some_and(|p| p.degree() > 0))
            })
            .flatten()
    })?;
    let u = &factors[u_index];
    let dv = Term::Mul(Mul::new(
        malachite::Rational::from(1),
        factors
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != u_index)
            .map(|(_, factor)| factor.clone())
            .collect(),
        R,
    ))
    .normalize();
    let v = integrator.integrate(&dv, x)?;
    let rest = integrator.integrate(&(u.derivative(x) * &v).expand(), x)?;
    Some(u * &v - rest)
}

/// Whether `term` is a logarithm or an inverse function, or a positive integer power of one.
fn is_logarithmic(term: &Expr) -> bool {
    let base = match term {
        Term::Pow(pow) if pow.exponant.to_i64().is_some_and(|n| n > 0) => &*pow.base,
        _ => term,
    };
    matches!(
        unary(base),
        Some((
            Context::LN
                | Context::ASIN
                | Context::ACOS
                | Context::ATAN
                | Context::ASINH
                | Context::ACOSH
                | Context::ATANH,
            _
        ))
    )
}
