//! Global extrema: the points where a function reaches its minimum or maximum, `argmin(x^4 - 2 x^2, x)`,
//! `argmax(x - x^2, x, 0, 2)` or `argmin(x^2 + y^2 - 2 x, x, y)`.
//!
//! A function of one variable is minimized over ℝ or over `{$[a, b]$}` by comparing its values at its critical
//! points, at the points where it isn't differentiable or stops being defined, and at the bounds, with its limits
//! at the ends of the intervals where it is defined: the minimum isn't reached when a limit is lower. A function
//! of several variables must be a rational function without parameters: the critical point with the lowest value
//! is the minimum when `{$f < m$}` has no solution, found by the cylindrical algebraic decomposition, otherwise
//! there is no minimum, every minimizer of a differentiable function on an open set being a critical point.
//!
//! ```
//! use formalith::{field::real::R, optimize::Optimize, parse, solve::Solution, symbol};
//!
//! let x = symbol!("x");
//! let optimum = R.optimize(&parse!("x^2 - 2*x", R), &[x], None, false).unwrap();
//! assert_eq!(optimum.solution, Solution::Assignments(vec![(x, parse!("1", R))]));
//! ```

mod multivariate;
mod univariate;

use std::cmp::Ordering;

use crate::{
    context::Symbol,
    field::{
        Set,
        real::{
            Real,
            expr::{Expr, constant_sign, depends, zero},
        },
    },
    solve::{Equation, Solution, SolveError},
    term::{Expand, Normalize, Term},
};

/// The minimizers or maximizers of a function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Optimum<T: Set> {
    /// The equations of the critical points, `{$diff f / diff x_i = 0$}` for each unknown.
    pub equations: Vec<Equation<T>>,
    /// The points where the extremum is reached, [`Solution::NoSolution`] when it isn't, like for `{$e^x$}`.
    pub solution: Solution<T>,
}

/// Sets in which global extrema can be found: only [`R`](crate::field::real::R), other sets fail at runtime.
pub trait Optimize: Set {
    /// The points where `f` reaches its global minimum (its maximum when `maximize` is `true`) over the real
    /// values of `unknowns`, or over `{$[a, b]$}` for `bounds` `(a, b)` and a single unknown.
    ///
    /// # Errors
    /// [`SolveError::Optimization`] when the extremum can't be decided: equations that can't be solved, values or
    /// limits that can't be compared, several variables in a function that isn't rational or with parameters.
    fn optimize(
        &self,
        f: &Term<Self>,
        unknowns: &[Symbol],
        bounds: Option<&(Term<Self>, Term<Self>)>,
        maximize: bool,
    ) -> Result<Optimum<Self>, SolveError>;
}

impl<T: Set> Optimize for T {
    default fn optimize(
        &self,
        _: &Term<Self>,
        _: &[Symbol],
        _: Option<&(Term<Self>, Term<Self>)>,
        _: bool,
    ) -> Result<Optimum<Self>, SolveError> {
        Err(SolveError::Unsupported)
    }
}

impl Optimize for Real {
    fn optimize(
        &self,
        f: &Expr,
        unknowns: &[Symbol],
        bounds: Option<&(Expr, Expr)>,
        maximize: bool,
    ) -> Result<Optimum<Self>, SolveError> {
        profile_scope!("optimize");
        let equations: Vec<_> = unknowns
            .iter()
            .map(|x| Equation::new(f.derivative(*x).normalize(), zero()))
            .collect();
        let f = if maximize { -f } else { f.clone() };
        let solution = if unknowns.iter().all(|x| !depends(&f, *x)) {
            // A constant function reaches its extremum everywhere
            Solution::Assignments(vec![])
        } else if let [x] = unknowns {
            univariate::argmin(&f, *x, bounds, &equations[0])?
        } else if bounds.is_some() {
            return Err(error("bounds are only supported for a single variable"));
        } else {
            multivariate::argmin(&f, unknowns, &equations)?
        };
        Ok(Optimum {
            equations,
            solution,
        })
    }
}

/// An error with `reason`.
fn error(reason: impl Into<String>) -> SolveError {
    SolveError::Optimization(reason.into())
}

/// Compare `p` and `q`, exactly when their difference is zero once expanded, otherwise from its sign (structure,
/// assumptions, then approximation of constants). `None` when it is unknown.
fn compare(p: &Expr, q: &Expr) -> Option<Ordering> {
    let difference = (p.clone() - q.clone()).normalize();
    if difference.is_zero() || difference.expand().is_zero() {
        return Some(Ordering::Equal);
    }
    constant_sign(&difference)
}

/// Keep in `best` the candidates with the lowest value, adding `candidate` with its `value`.
fn keep_lowest<P>(best: &mut Vec<(P, Expr)>, candidate: P, value: Expr) -> Result<(), SolveError> {
    let Some((_, lowest)) = best.first() else {
        best.push((candidate, value));
        return Ok(());
    };
    match compare(&value, lowest) {
        Some(Ordering::Less) => *best = vec![(candidate, value)],
        Some(Ordering::Equal) => best.push((candidate, value)),
        Some(Ordering::Greater) => {}
        None => {
            return Err(error(format!(
                "can't compare the values `{}` and `{}`",
                crate::solve::plain(&value),
                crate::solve::plain(lowest)
            )));
        }
    }
    Ok(())
}
