//! Global minimum of a function of one variable, over ℝ or over `{$[a, b]$}`.
//!
//! The domain is cut at the special points: the bounds, the zeros of the arguments of `ln`, of the bases of
//! fractional or negative powers and of the other functions defined on intervals (where `f` may stop being
//! defined), of the arguments of `abs` and `sign`, and of the denominator of `{$f'$}` (where `f` may not be
//! differentiable). On each open interval between them where `f` is defined (checked at a sample point), its
//! minimum can only be at a critical point, a zero of `{$f'$}`. The minimum is the lowest value at the critical
//! points and at the special points where `f` is defined, unless a limit at the end of an interval is lower, or
//! the lowest value isn't reached when there is no such point.
//!
//! Periodic critical points `{$c(k)$}`, `k` being an integer parameter, are listed on finite intervals, and kept
//! over ℝ when `{$f(c(k))$}` doesn't depend on `k` (limits at infinity then don't exist, as `f` oscillates).

use std::cmp::Ordering;

use malachite::{
    Integer, Rational,
    base::num::arithmetic::traits::{Ceiling, Floor, Parity, Sign},
};

use super::{compare, error, keep_lowest};
use crate::{
    context::{
        Context, Symbol,
        assumptions::{Assumption, Assumptions},
    },
    field::real::{
        R, Real,
        approx::approximate,
        expr::{
            DIGITS, Expr, constant_sign, depends, fun, half, has_special_constant, infinity,
            infinity_sign, is_infinite, one, subs, try_map_operands, value, zero,
        },
        sign::is_integer,
    },
    limit::{Direction, LimitError},
    solve::{Equation, Solution, Solve, SolveError, is_integer_parameter, plain},
    term::{Expand, Normalize, Term},
};

/// The most points a periodic solution gives on a finite interval.
const MAX_PERIODIC_POINTS: i64 = 100;

/// A condition for `f` to be defined, on a subterm `u`.
#[derive(Clone, Copy, Debug)]
enum Condition {
    /// `{$u > 0$}`, like in `{$ln u$}`
    Positive,
    /// `{$u >= 0$}`, like in `{$sqrt(u)$}`
    NonNegative,
    /// `{$u != 0$}`, like in `{$1/u$}`
    NonZero,
}

impl Condition {
    /// Whether a term of sign `sign` satisfies the condition.
    fn holds(self, sign: Ordering) -> bool {
        match self {
            Self::Positive => sign == Ordering::Greater,
            Self::NonNegative => sign != Ordering::Less,
            Self::NonZero => sign != Ordering::Equal,
        }
    }
}

/// The minimizers of `f` in `x`, over `bounds` (ℝ by default). `derivative` is `{$f' = 0$}`.
pub(super) fn argmin(
    f: &Expr,
    x: Symbol,
    bounds: Option<&(Expr, Expr)>,
    derivative: &Equation<Real>,
) -> Result<Solution<Real>, SolveError> {
    let (a, b) = bounds.cloned().unwrap_or_else(|| (-infinity(), infinity()));
    if depends(&a, x) || depends(&b, x) {
        return Err(error(format!("the bounds can't depend on `{}`", x.name())));
    }
    if infinity_sign(&a) == Some(Ordering::Greater) || infinity_sign(&b) == Some(Ordering::Less) {
        return Err(error("the lower bound must be below the upper bound"));
    }
    if has_step(f) {
        return Err(error("`floor`, `ceil` and `piecewise` aren't supported"));
    }
    let (lower, upper) = (finite(&a), finite(&b));
    if let (Some(a), Some(b)) = (lower, upper)
        && compare(a, b) != Some(Ordering::Less)
    {
        return Err(error(format!(
            "can't check that `{}` is below `{}`",
            plain(a),
            plain(b)
        )));
    }
    let mut conditions = vec![];
    collect_conditions(f, x, &mut conditions);
    // Special points, where `f` may stop being defined or differentiable
    let mut special = vec![];
    for (u, _) in &conditions {
        special.extend(zeros(u, x)?);
    }
    let steps = step_arguments(f, x);
    for u in &steps {
        special.extend(zeros(u, x)?);
    }
    let (_, denominator) = derivative.lhs.as_fraction(true);
    if depends(&denominator, x) {
        special.extend(zeros(&denominator, x)?);
    }
    // Integer parameters of periodic solutions
    let used = f.symbols();
    let parameters = |point: &Expr| -> Vec<Symbol> {
        point
            .symbols()
            .into_iter()
            .filter(|s| is_integer_parameter(*s) && !used.contains(s))
            .collect()
    };
    let (special, special_families) = periodic(special, &parameters, lower, upper)?;
    if !special_families.is_empty() {
        return Err(error(
            "infinitely many points where the function isn't defined or differentiable",
        ));
    }
    // With `abs` or `sign`, critical points are found on each interval, where their signs are constant
    let (critical, families) = if steps.is_empty() {
        let critical = roots(R.solve_for(std::slice::from_ref(derivative), &[x])?, x)?;
        periodic(critical, &parameters, lower, upper)?
    } else {
        (vec![], vec![])
    };
    // The points cutting the domain, sorted
    let mut points: Vec<Expr> = vec![];
    for point in lower.into_iter().chain(upper) {
        insert_sorted(&mut points, point.clone())?;
    }
    for point in special {
        if is_inside(&point, lower, upper, true)? {
            insert_sorted(&mut points, point)?;
        }
    }
    if !families.is_empty() && !points.is_empty() {
        return Err(error(
            "periodic critical points are only supported over ℝ for functions defined and differentiable everywhere",
        ));
    }
    // The open intervals between the points, `None` being an infinite end, kept when `f` is defined there
    let mut intervals: Vec<(Option<&Expr>, Option<&Expr>)> = vec![];
    if lower.is_none() {
        intervals.push((None, points.first()));
    }
    intervals.extend(points.windows(2).map(|w| (Some(&w[0]), Some(&w[1]))));
    if upper.is_none() && !points.is_empty() {
        intervals.push((points.last(), None));
    }
    let mut defined = vec![];
    for interval in intervals {
        if is_defined(&conditions, x, &sample(interval))? {
            defined.push(interval);
        }
    }
    // Limits at the ends of the intervals where `f` is defined, from inside
    let mut limits = vec![];
    for (l, r) in &defined {
        limits.push(match l {
            Some(l) => (*l, f.limit(x, l, Direction::Right)),
            None => (&a, f.limit(x, &a, Direction::Both)),
        });
        limits.push(match r {
            Some(r) => (*r, f.limit(x, r, Direction::Left)),
            None => (&b, f.limit(x, &b, Direction::Both)),
        });
    }
    if limits
        .iter()
        .any(|(_, limit)| matches!(limit, Ok(l) if infinity_sign(l) == Some(Ordering::Less)))
    {
        return Ok(Solution::NoSolution);
    }
    // Candidates: special points where `f` is defined, critical points inside an interval where it is defined,
    // and intervals where `f` is constant, with a sample point
    let mut candidates: Vec<(Expr, Option<(Option<&Expr>, Option<&Expr>)>)> = vec![];
    for point in &points {
        if is_defined(&conditions, x, point)? {
            candidates.push((point.clone(), None));
        }
    }
    for point in critical {
        if !is_inside(&point, lower, upper, false)?
            || points
                .iter()
                .any(|p| compare(p, &point) == Some(Ordering::Equal))
        {
            continue;
        }
        for (l, r) in &defined {
            if is_inside(&point, *l, *r, true)? {
                candidates.push((point, None));
                break;
            }
        }
    }
    if !steps.is_empty() {
        for &(l, r) in &defined {
            let at = sample((l, r));
            let g = without_steps(f, x, &at)?;
            let derivative = Equation::new(g.derivative(x).normalize(), zero());
            if derivative.lhs.expand().is_zero() {
                candidates.push((at, Some((l, r))));
                continue;
            }
            let critical = roots(R.solve_for(&[derivative], &[x])?, x)?;
            let (critical, families) = periodic(critical, &parameters, l, r)?;
            if !families.is_empty() {
                return Err(error(format!(
                    "periodic critical points of `{}` on an infinite interval",
                    plain(&g)
                )));
            }
            for point in critical {
                if is_inside(&point, l, r, true)? {
                    candidates.push((point, None));
                }
            }
        }
    }
    let oscillating = !families.is_empty() && !defined.is_empty();
    if oscillating {
        candidates.extend(families.into_iter().map(|point| (point, None)));
    }
    // The integer parameters of periodic points are assumed integers while evaluating `f`
    let mut assumptions = Assumptions::current();
    for (point, _) in &candidates {
        for k in parameters(point) {
            assumptions.assume(k, Assumption::INTEGER).map_err(error)?;
        }
    }
    let _guard = assumptions.enter();
    let mut best = vec![];
    for (point, interval) in candidates {
        let value = subs(f, x, &point).expand();
        if has_special_constant(&value) {
            continue;
        }
        if let Some(k) = parameters(&point).first()
            && depends(&value, *k)
        {
            return Err(error(format!(
                "the value `{}` at the periodic point `{}` depends on `{}`",
                plain(&value),
                plain(&point),
                k.name()
            )));
        }
        keep_lowest(&mut best, (point, interval), value)?;
    }
    let Some((_, lowest)) = best.first() else {
        return Ok(Solution::NoSolution);
    };
    if let Some(&((_, Some((l, r))), _)) = best.iter().find(|((_, interval), _)| interval.is_some())
    {
        let end =
            |end: Option<&Expr>, infinite: &str| end.map_or_else(|| infinite.to_owned(), plain);
        return Err(error(format!(
            "the extremum is reached on the whole interval ({}, {})",
            end(l, "-oo"),
            end(r, "oo")
        )));
    }
    for (point, limit) in limits {
        let at = || format!("the limit of `{}` at `{}`", plain(f), plain(point));
        match limit {
            Ok(l) if infinity_sign(&l) == Some(Ordering::Greater) => {}
            Ok(l) if !has_special_constant(&l) => match compare(&l, lowest) {
                Some(Ordering::Less) => return Ok(Solution::NoSolution),
                Some(_) => {}
                None => {
                    return Err(error(format!(
                        "can't compare {} with `{}`",
                        at(),
                        plain(lowest)
                    )));
                }
            },
            Ok(ref l) if !depends(l, Context::UNDEFINED) => {
                return Err(error(format!("can't decide {}, `{}`", at(), plain(l))));
            }
            Ok(_) | Err(LimitError::Undefined) if oscillating && is_infinite(point) => {}
            Ok(_) | Err(LimitError::Undefined) => {
                return Err(error(format!("{} doesn't exist", at())));
            }
            Err(_) => return Err(error(format!("can't find {}", at()))),
        }
    }
    Ok(Solution::from_branches(
        best.into_iter()
            .map(|((point, _), _)| vec![(x, point)])
            .collect(),
    ))
}

/// `Some(bound)` for a finite bound.
fn finite(bound: &Expr) -> Option<&Expr> {
    (!is_infinite(bound)).then_some(bound)
}

/// `term` with `{$abs(u) = plus.minus u$}` and `{$sign(u) = plus.minus 1$}` for the arguments depending on `x`, by
/// their sign at `sample`, which isn't one of their zeros.
fn without_steps(term: &Expr, x: Symbol, sample: &Expr) -> Result<Expr, SolveError> {
    if !depends(term, x) {
        return Ok(term.clone());
    }
    if let Term::Fun(function) = term
        && let ident @ (Context::ABS | Context::SIGN) = function.get_ident()
        && let Some(arg) = function.get_arg::<Real>()
    {
        let arg = without_steps(arg, x, sample)?;
        let at = subs(&arg, x, sample);
        let unit = match constant_sign(&at) {
            Some(Ordering::Greater) => one(),
            Some(Ordering::Less) => -one(),
            _ => {
                return Err(error(format!("can't find the sign of `{}`", plain(&at))));
            }
        };
        return Ok(if ident == Context::ABS {
            (unit * arg).normalize()
        } else {
            unit
        });
    }
    try_map_operands(term, |t| without_steps(t, x, sample))
}

/// Whether `term` contains `floor`, `ceil` or `piecewise`, whose jumps aren't found.
fn has_step(term: &Expr) -> bool {
    match term {
        Term::Value(_) | Term::Symbol(_) => false,
        Term::Add(add) => add.iter().any(has_step),
        Term::Mul(mul) => mul.iter().any(has_step),
        Term::Pow(pow) => has_step(&pow.base) || has_step(&pow.exponant),
        Term::Fun(function) => {
            matches!(
                function.get_ident(),
                Context::FLOOR | Context::CEIL | Context::PIECEWISE
            ) || function
                .get_args::<Real>()
                .is_some_and(|args| args.iter().any(has_step))
        }
    }
}

/// The arguments depending on `x` of `abs` and `sign` in `term`, where it may not be differentiable.
fn step_arguments(term: &Expr, x: Symbol) -> Vec<Expr> {
    let mut res = vec![];
    let mut visit = |t: &Expr| {
        if let Term::Fun(function) = t
            && matches!(function.get_ident(), Context::ABS | Context::SIGN)
            && let Some(arg) = function.get_arg::<Real>()
            && depends(arg, x)
        {
            res.push(arg.clone());
        }
    };
    walk(term, &mut visit);
    res
}

/// Call `visit` on every subterm of `term`.
fn walk(term: &Expr, visit: &mut impl FnMut(&Expr)) {
    visit(term);
    match term {
        Term::Value(_) | Term::Symbol(_) => {}
        Term::Add(add) => add.iter().for_each(|t| walk(t, visit)),
        Term::Mul(mul) => mul.iter().for_each(|t| walk(t, visit)),
        Term::Pow(pow) => {
            walk(&pow.base, visit);
            walk(&pow.exponant, visit);
        }
        Term::Fun(function) => {
            if let Some(args) = function.get_args::<Real>() {
                args.iter().for_each(|t| walk(t, visit));
            }
        }
    }
}

/// Push to `res` the conditions for `term` to be defined, those of its subterms first.
fn collect_conditions(term: &Expr, x: Symbol, res: &mut Vec<(Expr, Condition)>) {
    if !depends(term, x) {
        return;
    }
    match term {
        Term::Value(_) | Term::Symbol(_) => {}
        Term::Add(add) => add.iter().for_each(|t| collect_conditions(t, x, res)),
        Term::Mul(mul) => mul.iter().for_each(|t| collect_conditions(t, x, res)),
        Term::Pow(pow) => {
            collect_conditions(&pow.base, x, res);
            collect_conditions(&pow.exponant, x, res);
            let (base, exponent): (&Expr, &Expr) = (&pow.base, &pow.exponant);
            if !depends(base, x) {
                return;
            }
            match exponent {
                Term::Value(e) => {
                    if e.value.sign() == Ordering::Less {
                        res.push((base.clone(), Condition::NonZero));
                    }
                    if e.value.denominator_ref().even() {
                        res.push((base.clone(), Condition::NonNegative));
                    }
                }
                e if !is_integer(e) => res.push((base.clone(), Condition::Positive)),
                _ => {}
            }
        }
        Term::Fun(function) => {
            let Some(args) = function.get_args::<Real>() else {
                return;
            };
            args.iter().for_each(|t| collect_conditions(t, x, res));
            let [u] = args.as_slice() else {
                return;
            };
            let square = || (one() - u.pow(&value(Rational::from(2)))).normalize();
            match function.get_ident() {
                Context::LN => res.push((u.clone(), Condition::Positive)),
                Context::TAN => res.push((fun(Context::COS, u.clone()), Condition::NonZero)),
                Context::ASIN | Context::ACOS => res.push((square(), Condition::NonNegative)),
                Context::ATANH => res.push((square(), Condition::Positive)),
                Context::ACOSH => res.push(((u - &one()).normalize(), Condition::NonNegative)),
                Context::LAMBERTW => res.push((
                    (u.clone() + fun(Context::EXP, -one())).normalize(),
                    Condition::NonNegative,
                )),
                _ => {}
            }
        }
    }
}

/// Whether every condition holds at `x = point`, in order, so that a condition is only evaluated where the
/// previous ones hold.
fn is_defined(
    conditions: &[(Expr, Condition)],
    x: Symbol,
    point: &Expr,
) -> Result<bool, SolveError> {
    for (u, condition) in conditions {
        let at = subs(u, x, point);
        let sign = constant_sign(&at)
            .ok_or_else(|| error(format!("can't find the sign of `{}`", plain(&at))))?;
        if !condition.holds(sign) {
            return Ok(false);
        }
    }
    Ok(true)
}

/// The values of `x` such that `u = 0`.
fn zeros(u: &Expr, x: Symbol) -> Result<Vec<Expr>, SolveError> {
    roots(R.solve_for(&[Equation::new(u.clone(), zero())], &[x])?, x)
}

/// The values of `x` of a solution for `x` alone.
fn roots(solution: Solution<Real>, x: Symbol) -> Result<Vec<Expr>, SolveError> {
    let branches = match solution {
        Solution::NoSolution => return Ok(vec![]),
        Solution::Assignments(assignments) => vec![assignments],
        Solution::Alternatives(branches) => branches,
    };
    branches
        .into_iter()
        .map(|branch| match branch.as_slice() {
            [(symbol, point)] if *symbol == x => Ok(point.clone()),
            _ => Err(error(format!(
                "the derivative or a denominator vanishes for every `{}`",
                x.name()
            ))),
        })
        .collect()
}

/// Split `points` into points and periodic families, listing the points of the families on the finite interval
/// `{$[a, b]$}`.
fn periodic(
    points: Vec<Expr>,
    parameters: &impl Fn(&Expr) -> Vec<Symbol>,
    lower: Option<&Expr>,
    upper: Option<&Expr>,
) -> Result<(Vec<Expr>, Vec<Expr>), SolveError> {
    let (mut res, mut families) = (vec![], vec![]);
    for point in points {
        match (parameters(&point).as_slice(), lower, upper) {
            ([], _, _) => res.push(point),
            ([k], Some(a), Some(b)) => res.extend(list_periodic(&point, *k, a, b)?),
            ([_], _, _) => families.push(point),
            _ => {
                return Err(error(format!(
                    "the periodic point `{}` has several parameters",
                    plain(&point)
                )));
            }
        }
    }
    Ok((res, families))
}

/// The points `{$alpha k + beta$}` of `point` for the integers `k` around `{$[a, b]$}`, which are checked later.
fn list_periodic(point: &Expr, k: Symbol, a: &Expr, b: &Expr) -> Result<Vec<Expr>, SolveError> {
    let unsupported = || {
        error(format!(
            "can't list the values of the periodic point `{}` between `{}` and `{}`",
            plain(point),
            plain(a),
            plain(b)
        ))
    };
    let alpha = point.derivative(k).normalize();
    let beta = subs(point, k, &zero());
    if depends(&alpha, k) || alpha.is_zero() {
        return Err(unsupported());
    }
    let index = |bound: &Expr| {
        approximate(
            &((bound.clone() - beta.clone()) / alpha.clone()).normalize(),
            DIGITS,
        )
        .ok_or_else(unsupported)
    };
    let (i, j) = (index(a)?, index(b)?);
    let (low, high) = if i <= j { (i, j) } else { (j, i) };
    let to_i64 = |n: Integer| i64::try_from(&n).map_err(|_| unsupported());
    let (low, high) = (to_i64((&low).floor())?, to_i64((&high).ceiling())?);
    if high - low > MAX_PERIODIC_POINTS {
        return Err(unsupported());
    }
    Ok((low..=high)
        .map(|n| subs(point, k, &value(Rational::from(n))))
        .collect())
}

/// Whether `point` is between `lower` and `upper` (`None` being infinite), strictly or not.
fn is_inside(
    point: &Expr,
    lower: Option<&Expr>,
    upper: Option<&Expr>,
    strict: bool,
) -> Result<bool, SolveError> {
    let below = |p: &Expr, q: &Expr| {
        compare(p, q)
            .map(|ordering| ordering == Ordering::Less || (!strict && ordering == Ordering::Equal))
            .ok_or_else(|| error(format!("can't compare `{}` and `{}`", plain(p), plain(q))))
    };
    Ok(lower.map_or(Ok(true), |a| below(a, point))?
        && upper.map_or(Ok(true), |b| below(point, b))?)
}

/// Insert `point` in the sorted `points` if it isn't there.
fn insert_sorted(points: &mut Vec<Expr>, point: Expr) -> Result<(), SolveError> {
    for (i, other) in points.iter().enumerate() {
        match compare(&point, other) {
            Some(Ordering::Equal) => return Ok(()),
            Some(Ordering::Less) => {
                points.insert(i, point);
                return Ok(());
            }
            Some(Ordering::Greater) => {}
            None => {
                return Err(error(format!(
                    "can't compare `{}` and `{}`",
                    plain(&point),
                    plain(other)
                )));
            }
        }
    }
    points.push(point);
    Ok(())
}

/// A point inside an open interval.
fn sample((l, r): (Option<&Expr>, Option<&Expr>)) -> Expr {
    match (l, r) {
        (Some(l), Some(r)) => ((l.clone() + r.clone()) * half()).normalize(),
        (Some(l), None) => (l.clone() + one()).normalize(),
        (None, Some(r)) => (r.clone() - one()).normalize(),
        (None, None) => zero(),
    }
}
