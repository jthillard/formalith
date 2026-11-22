//! Global minimum of a rational function of several variables, without parameters.
//!
//! A minimizer of a function differentiable on an open set is a critical point, so the minimum is the lowest value
//! `m` of `f` at the solutions of `{$nabla f = 0$}` when `{$f < m$}` has no solution (cylindrical algebraic
//! decomposition), and isn't reached otherwise. Families of critical points along which `f` isn't constant are
//! dropped.

use super::{error, keep_lowest};
use crate::{
    context::{Context, Symbol},
    field::real::{
        R, Real,
        expr::{Expr, depends, has_special_constant, subs},
    },
    solve::{
        Equation, Solution, Solve, SolveError,
        inequality::{Inequality, SolveInequality},
    },
    sum::is_rational_function,
    term::{Expand, relation::Relation},
};

/// The minimizers of `f` in `unknowns`, `equations` being `{$diff f / diff x_i = 0$}`.
pub(super) fn argmin(
    f: &Expr,
    unknowns: &[Symbol],
    equations: &[Equation<Real>],
) -> Result<Solution<Real>, SolveError> {
    if !is_rational_function(f) {
        return Err(error(
            "functions of several variables must be rational functions",
        ));
    }
    if let Some(parameter) = f
        .symbols()
        .into_iter()
        .find(|s| !unknowns.contains(s) && !Context::is_builtin_constant(*s))
    {
        return Err(error(format!(
            "functions of several variables can't have parameters, like `{}`",
            parameter.name()
        )));
    }
    let branches = match R.solve_for(equations, unknowns)? {
        Solution::NoSolution => return Ok(Solution::NoSolution),
        Solution::Assignments(assignments) => vec![assignments],
        Solution::Alternatives(branches) => branches,
    };
    let mut best = vec![];
    for branch in branches {
        let value = branch
            .iter()
            .fold(f.clone(), |res, (symbol, point)| subs(&res, *symbol, point))
            .expand();
        if has_special_constant(&value) || unknowns.iter().any(|x| depends(&value, *x)) {
            continue;
        }
        keep_lowest(&mut best, branch, value)?;
    }
    let Some((_, lowest)) = best.first() else {
        return Ok(Solution::NoSolution);
    };
    let below = Inequality::new(f.clone(), Relation::Less, lowest.clone());
    if !R.solve_inequalities(&[below], unknowns)?.cells.is_empty() {
        return Ok(Solution::NoSolution);
    }
    Ok(Solution::from_branches(
        best.into_iter().map(|(branch, _)| branch).collect(),
    ))
}
