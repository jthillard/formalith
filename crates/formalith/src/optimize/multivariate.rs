//! Global minimum of a rational function of several variables, without parameters.
//!
//! A minimizer of a function differentiable on an open set is a critical point, so the minimum is the lowest value
//! `m` of `f` at the solutions of `{$nabla f = 0$}` when `{$f < m$}` has no solution (cylindrical algebraic
//! decomposition), and isn't reached otherwise. Families of critical points along which `f` isn't constant are
//! dropped.
//!
//! Local minima are the critical points where the Hessian matrix is positive definite (all its leading principal
//! minors are positive). Degenerate critical points (a singular Hessian matrix) and lines of critical points are
//! local minima when they are global ones, and not when they are global maxima, otherwise they can't be classified.

use std::cmp::Ordering;

use malachite::base::num::arithmetic::traits::Sign;

use super::{
    error, keep_lowest,
    univariate::{Condition, domain_conditions},
};
use crate::{
    context::{Context, Symbol},
    field::{
        Set,
        real::{
            R, Real,
            approx::approximate,
            expr::{DIGITS, Expr, constant_sign, depends, has_special_constant, subs},
        },
    },
    matrix::Matrix,
    solve::{
        Assignments, Equation, Solution, Solve, SolveError,
        inequality::{Inequality, SolveInequality},
        plain,
    },
    sum::is_rational_function,
    term::{Expand, Normalize, Term, relation::Relation},
};

/// The kind of a critical point, from its Hessian matrix.
enum Kind {
    /// A local minimum, the Hessian matrix being positive definite
    Minimum,
    /// A local maximum, the Hessian matrix being negative definite
    Maximum,
    /// Neither, the Hessian matrix being invertible and indefinite
    Saddle,
    /// The Hessian matrix is singular
    Degenerate,
}

/// The conditions for `f` to be defined, with those of the terms of `domain`, each once.
fn conditions(f: &Expr, domain: &[Expr], unknowns: &[Symbol]) -> Vec<(Expr, Condition)> {
    let mut res: Vec<(Expr, Condition)> = vec![];
    for x in unknowns {
        for condition in domain_conditions(f, domain, *x) {
            if !res.contains(&condition) {
                res.push(condition);
            }
        }
    }
    res
}

/// The minimizers of `f` in `unknowns`, `equations` being `{$diff f / diff x_i = 0$}`, `f` being only defined
/// where the terms of `domain` are.
pub(super) fn argmin(
    f: &Expr,
    domain: &[Expr],
    unknowns: &[Symbol],
    equations: &[Equation<Real>],
) -> Result<Solution<Real>, SolveError> {
    check_rational(f, unknowns)?;
    let conditions = conditions(f, domain, unknowns);
    let mut best = vec![];
    for (branch, value) in critical_points(f, &conditions, unknowns, equations)? {
        keep_lowest(&mut best, branch, value)?;
    }
    let Some((_, lowest)) = best.first() else {
        return Ok(Solution::NoSolution);
    };
    if !is_bound(f, &conditions, unknowns, lowest, Relation::Less)? {
        return Ok(Solution::NoSolution);
    }
    Ok(Solution::from_branches(
        best.into_iter().map(|(branch, _)| branch).collect(),
    ))
}

/// The local minimizers of `f` in `unknowns`, `equations` being `{$diff f / diff x_i = 0$}`, `f` being only
/// defined where the terms of `domain` are.
pub(super) fn local_min(
    f: &Expr,
    domain: &[Expr],
    unknowns: &[Symbol],
    equations: &[Equation<Real>],
) -> Result<Solution<Real>, SolveError> {
    let gradient: Vec<Expr> = unknowns
        .iter()
        .map(|x| f.derivative(*x).normalize())
        .collect();
    let hessian: Vec<Vec<Expr>> = gradient
        .iter()
        .map(|g| {
            unknowns
                .iter()
                .map(|x| g.derivative(*x).normalize())
                .collect()
        })
        .collect();
    let minors = leading_minors(&hessian)?;
    let conditions = conditions(f, domain, unknowns);
    let mut minimizers = vec![];
    for (branch, value) in critical_points(f, &conditions, unknowns, equations)? {
        let is_point = unknowns
            .iter()
            .all(|x| branch.iter().any(|(symbol, _)| symbol == x));
        let kind = if is_point {
            classify(&minors, &branch)?
        } else {
            Kind::Degenerate
        };
        let is_min = match kind {
            Kind::Minimum => true,
            Kind::Maximum | Kind::Saddle => false,
            Kind::Degenerate => {
                check_rational(f, unknowns).map_err(|_| {
                    error(format!(
                        "can't classify the degenerate critical point {}",
                        assignments_text(&branch)
                    ))
                })?;
                if is_bound(f, &conditions, unknowns, &value, Relation::Less)? {
                    true
                } else if is_bound(f, &conditions, unknowns, &value, Relation::Greater)? {
                    false
                } else {
                    return Err(error(format!(
                        "can't classify the degenerate critical point {}",
                        assignments_text(&branch)
                    )));
                }
            }
        };
        if is_min {
            minimizers.push(branch);
        }
    }
    Ok(Solution::from_branches(minimizers))
}

/// Check that `f` is a rational function of `unknowns` without parameters, as required by the cylindrical
/// algebraic decomposition.
fn check_rational(f: &Expr, unknowns: &[Symbol]) -> Result<(), SolveError> {
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
    Ok(())
}

/// The critical points of `f` with its value there, dropping those where it isn't defined (by its value, or a
/// constant violating one of `conditions` there) and the lines of critical points along which it isn't constant.
fn critical_points(
    f: &Expr,
    conditions: &[(Expr, Condition)],
    unknowns: &[Symbol],
    equations: &[Equation<Real>],
) -> Result<Vec<(Assignments<Real>, Expr)>, SolveError> {
    let branches = match R.solve_for(equations, unknowns)? {
        Solution::NoSolution => vec![],
        Solution::Assignments(assignments) => vec![assignments],
        Solution::Alternatives(branches) => branches,
    };
    Ok(branches
        .into_iter()
        .filter_map(|branch| {
            let value = at(f, &branch);
            let defined = conditions.iter().all(|(u, condition)| {
                let u = at(u, &branch);
                unknowns.iter().any(|x| depends(&u, *x))
                    || constant_sign(&u).is_none_or(|sign| condition.holds(sign))
            });
            (defined
                && !has_special_constant(&value)
                && !unknowns.iter().any(|x| depends(&value, *x)))
            .then_some((branch, value))
        })
        .collect())
}

/// `term` at the point given by `assignments`.
fn at(term: &Expr, assignments: &Assignments<Real>) -> Expr {
    assignments
        .iter()
        .fold(term.clone(), |res, (symbol, point)| {
            subs(&res, *symbol, point)
        })
        .expand()
}

/// Whether `{$f op m$}` has no solution where `conditions` hold: `m` is a lower bound of `f` for
/// [`Relation::Less`], an upper bound for [`Relation::Greater`].
///
/// `m` must be rational: the cylindrical algebraic decomposition factors over ℚ, and with radicals (values at
/// roots of cubics) it fails or doesn't finish.
fn is_bound(
    f: &Expr,
    conditions: &[(Expr, Condition)],
    unknowns: &[Symbol],
    m: &Expr,
    relation: Relation,
) -> Result<bool, SolveError> {
    if !matches!(m, Term::Value(_)) {
        return Err(error(format!(
            "can't compare the function with the irrational value `{}`",
            plain(m)
        )));
    }
    let mut inequalities = vec![Inequality::new(f.clone(), relation, m.clone())];
    inequalities.extend(conditions.iter().map(|(u, condition)| {
        let relation = match condition {
            Condition::Positive => Relation::Greater,
            Condition::NonNegative => Relation::GreaterEqual,
            Condition::NonZero => Relation::NotEqual,
        };
        Inequality::new(u.clone(), relation, Term::zero(R))
    }));
    Ok(R.solve_inequalities(&inequalities, unknowns)?
        .cells
        .is_empty())
}

/// The leading principal minors of the Hessian matrix `hessian`, as functions of the unknowns.
fn leading_minors(hessian: &[Vec<Expr>]) -> Result<Vec<Expr>, SolveError> {
    (1..=hessian.len())
        .map(|k| {
            let entries = hessian[..k]
                .iter()
                .flat_map(|row| row[..k].iter().cloned())
                .collect();
            Ok(Matrix::new((k, k), entries, R.get_term_set())
                .det()
                .map_err(|_| error("can't compute a minor of the Hessian matrix"))?
                .expand())
        })
        .collect()
}

/// Classify a critical point by the signs of the leading principal minors `minors` of the Hessian matrix there.
///
/// The minors are substituted without expansion, which doesn't finish at points with nested radicals (roots of
/// quartics), and their signs are approximated: a minor which isn't zero but indistinguishable from it at the
/// maximum precision makes the point degenerate, decided by the global extrema, since a tiny non-zero minor would
/// change the kind.
fn classify(minors: &[Expr], point: &Assignments<Real>) -> Result<Kind, SolveError> {
    let n = minors.len();
    let mut signs = vec![];
    let mut undecided = false;
    for minor in minors {
        let minor = point
            .iter()
            .fold(minor.clone(), |res, (symbol, value)| {
                subs(&res, *symbol, value)
            })
            .normalize();
        let sign = match &minor {
            Term::Value(value) => Some(value.value.sign()),
            _ => approximate(&minor, DIGITS).map(|approximation| approximation.sign()),
        };
        if sign == Some(Ordering::Equal) && !minor.is_zero() {
            undecided = true;
        }
        let sign = sign.ok_or_else(|| {
            error(format!(
                "can't find the sign of `{}`, a minor of the Hessian matrix at {}",
                plain(&minor),
                assignments_text(point)
            ))
        })?;
        signs.push(sign);
    }
    Ok(if undecided || signs[n - 1] == Ordering::Equal {
        Kind::Degenerate
    } else if signs.iter().all(|sign| *sign == Ordering::Greater) {
        Kind::Minimum
    } else if signs.iter().enumerate().all(|(i, sign)| {
        *sign
            == if i % 2 == 0 {
                Ordering::Less
            } else {
                Ordering::Greater
            }
    }) {
        Kind::Maximum
    } else {
        Kind::Saddle
    })
}

/// The point `x = a, y = b` as text, for errors.
fn assignments_text(assignments: &Assignments<Real>) -> String {
    assignments
        .iter()
        .map(|(symbol, value)| format!("{} = {}", symbol.name(), plain(value)))
        .collect::<Vec<_>>()
        .join(", ")
}
