//! Homogeneous linear equations `{$sum_k a_k(x) y^((k)) = 0$}` with rational function coefficients, solved by
//! power series at an ordinary point `{$x_0$}` (where `{$a_k / a_n$}` has no pole), like the Airy equation
//! `{$y'' + x y = 0$}`.
//!
//! With `{$x = x_0 + w$}`, the coefficients `{$c_j$}` of `{$w^j$}` follow from the first `n` by the recurrence of
//! the equation, and the series of the solution `{$y_j$}` with `{$y_j^((i))(x_0) = delta_(i j)$}` is written as
//! held sums of its general terms when they have a proven closed form (see [`crate::sum::taylor::ode_series`]).
//! The solutions are `{$sum_j c_(j + 1) y_j$}`, the constants being the values of the derivatives at `{$x_0$}`, so
//! initial conditions at `{$x_0$}` fix them directly.

use malachite::Rational;

use crate::{
    context::Symbol,
    field::real::expr::{Expr, Real, depends, subs, value, variable, zero},
    holonomic::{
        dfinite,
        ore::{Kind, Operator},
        ratfun::RatFun,
    },
    polynom::{dense::Coefficient, fraction::Elem},
    solve::plain,
    sum::{field::Params, is_rational_function, taylor},
    term::Expand,
};

use super::{Condition, OdeBranch, OdeError, OdeResult};

/// Solve `{$sum_k a_k y^((k)) + "rest" = 0$}` for the `coefficients` `{$a_0, ..., a_n$}`, rational functions of
/// `x`, at the point of the `conditions` (0 without any), which fix the corresponding constants.
pub(super) fn solve(
    coefficients: &[Expr],
    rest: &Expr,
    x: Symbol,
    constants: &[Symbol],
    conditions: &[Condition<Real>],
) -> OdeResult<Vec<OdeBranch<Real>>> {
    let unsupported = |message: &str| OdeError::Unsupported(message.to_owned());
    if !rest.is_zero() {
        return Err(unsupported(
            "only homogeneous linear equations can be solved with non-constant coefficients",
        ));
    }
    if coefficients.iter().any(|a| !is_rational_function(a)) {
        return Err(unsupported(
            "the coefficients of a linear equation must be rational functions of the variable",
        ));
    }
    let point = conditions.first().map_or_else(zero, |c| c.point.clone());
    if conditions
        .iter()
        .any(|c| !(c.point.clone() - point.clone()).expand().is_zero())
    {
        return Err(unsupported(
            "the initial conditions of an equation with non-constant coefficients must be at the same point",
        ));
    }
    if depends(&point, x) || conditions.iter().any(|c| depends(&c.value, x)) {
        return Err(unsupported(
            "the initial conditions must not depend on the variable",
        ));
    }
    let w = Symbol::new("@ow");
    let mut params = Params::default();
    let shifted = point.clone() + variable(w);
    let a = coefficients
        .iter()
        .map(|a| dfinite::rational(&subs(a, x, &shifted), w, &mut params))
        .collect::<Option<Vec<_>>>()
        .ok_or_else(|| {
            unsupported("the coefficients of a linear equation must be rational functions")
        })?;
    let n = a.len() - 1;
    // `{$a_k / a_n$}`, without pole at the point
    let lead = &a[n];
    let normalized: Vec<RatFun> = a
        .iter()
        .map(|a_k| RatFun::new(&a_k.num.mul(&lead.den), &a_k.den.mul(&lead.num)))
        .collect();
    if normalized.iter().any(|a_k| {
        a_k.den
            .coefficients()
            .first()
            .is_none_or(Coefficient::is_zero)
    }) {
        return Err(OdeError::Unsupported(format!(
            "`{}` is a singular point of the equation",
            plain(&point)
        )));
    }
    let op = Operator::new(Kind::Differential, normalized)
        .ok_or_else(|| unsupported("the equation has no derivative"))?
        .clear_denominators();
    // The index of the sums, not a symbol of the equation nor a constant
    let used = constants.iter().fold(variable(x), |t, c| t + variable(*c));
    let used = coefficients.iter().fold(used, |t, a| t + a);
    let k = taylor::index(&used, &point);
    let w_of_x = variable(x) - point;
    // `{$c_i = y^((i))(x_0) / i!$}`
    let mut fixed = vec![Elem::zero(); n];
    let mut free = vec![];
    for (i, fixed) in fixed.iter_mut().enumerate() {
        match conditions.iter().find(|c| c.order == i) {
            Some(condition) => {
                let factorial = (1..=i).fold(Rational::from(1), |f, l| f * Rational::from(l));
                *fixed = params
                    .elem(&(condition.value.clone() / value(factorial)))
                    .ok_or_else(|| unsupported("invalid initial condition"))?;
            }
            None => free.push(i),
        }
    }
    let no_closed_form =
        || unsupported("no closed general term was found for the power series solutions");
    let series = |initial: &[Elem]| {
        taylor::ode_series(&op, initial, w_of_x.clone(), params.clone(), k)
            .ok_or_else(no_closed_form)
    };
    let mut res = zero();
    for (&i, c) in free.iter().zip(constants) {
        let factorial = (1..=i).fold(Rational::from(1), |f, l| f * Rational::from(l));
        let mut initial = vec![Elem::zero(); n];
        initial[i] = Elem::rational(Rational::from(1) / factorial);
        res += variable(*c) * series(&initial)?;
    }
    if fixed.iter().any(|c| !c.is_zero()) {
        res += series(&fixed)?;
    }
    Ok(vec![OdeBranch::Explicit(res)])
}
