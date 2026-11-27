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
//! over ℝ when `{$f(c(k))$}` doesn't depend on `k` (limits at infinity then don't exist, as `f` oscillates), after
//! splitting them into classes of `k` modulo a small `m` when that makes it so (`{$pi k$}` for `{$cos x$}`).
//!
//! Local minima, relative to the domain, use the same [`Analysis`]: a critical point is one when the derivative
//! goes from negative to positive (signs sampled between the sorted critical points of each interval), a special
//! point when `f` is above its value on each side where it is defined (one-sided limit, then the sign of the
//! derivative next to it), and a periodic critical point by the first non-vanishing derivative of order at least 2.

use std::cmp::Ordering;

use malachite::{
    Integer, Rational,
    base::num::arithmetic::traits::{Ceiling, Floor, Parity, Sign},
};

use super::{compare, error, keep_lowest};
use crate::{
    context::{
        Context, Symbol,
        assumptions::{Assumption, Assumptions, AssumptionsGuard},
    },
    field::real::{
        R, Real,
        approx::approximate,
        expr::{
            DIGITS, Expr, constant_sign, depends, fun, half, has_function, has_special_constant,
            infinity, infinity_sign, int, is_infinite, one, subs, try_map_operands, value,
            variable, zero,
        },
        sign::is_integer,
    },
    limit::{Direction, LimitError},
    solve::{
        Equation, Solution, Solve, SolveError, is_integer_parameter, is_natural_parameter, plain,
    },
    term::{Expand, Normalize, Term},
};

/// The most points a periodic solution gives on a finite interval.
const MAX_PERIODIC_POINTS: i64 = 100;

/// The highest order of the derivatives deciding whether a periodic critical point is a local extremum.
const MAX_DERIVATIVE_ORDER: usize = 6;

/// A condition for `f` to be defined, on a subterm `u`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Condition {
    /// `{$u > 0$}`, like in `{$ln u$}`
    Positive,
    /// `{$u >= 0$}`, like in `{$sqrt(u)$}`
    NonNegative,
    /// `{$u != 0$}`, like in `{$1/u$}`
    NonZero,
}

impl Condition {
    /// Whether a term of sign `sign` satisfies the condition.
    pub(super) fn holds(self, sign: Ordering) -> bool {
        match self {
            Self::Positive => sign == Ordering::Greater,
            Self::NonNegative => sign != Ordering::Less,
            Self::NonZero => sign != Ordering::Equal,
        }
    }
}

/// An open interval between two points of [`Analysis::points`] (`None` for an infinite end) where `f` is defined.
struct Piece {
    /// The index of the lower end.
    lower: Option<usize>,
    /// The index of the upper end.
    upper: Option<usize>,
    /// The derivative of `f` on the interval, with `abs` and `sign` written with their sign there.
    derivative: Expr,
    /// The critical points inside, sorted.
    critical: Vec<Expr>,
    /// Whether `f` is constant on the interval.
    flat: bool,
}

/// The domain of a function of one variable cut at its special points, with its critical points.
pub(super) struct Analysis<'a> {
    /// The function.
    f: &'a Expr,
    /// The variable.
    x: Symbol,
    /// The lower bound, possibly `{$-oo$}`.
    lower: Expr,
    /// The upper bound, possibly `{$oo$}`.
    upper: Expr,
    /// The conditions for `f` to be defined.
    conditions: Vec<(Expr, Condition)>,
    /// The finite bounds and the special points between them, where `f` may stop being defined or differentiable,
    /// sorted.
    points: Vec<Expr>,
    /// The intervals between the points where `f` is defined.
    pieces: Vec<Piece>,
    /// Periodic critical points `{$c(k)$}`, only over ℝ without special points.
    families: Vec<Expr>,
}

impl<'a> Analysis<'a> {
    /// Analyze `f` in `x` over `bounds` (ℝ by default), `f` being only defined where the terms of `domain` are.
    pub(super) fn new(
        f: &'a Expr,
        domain: &[Expr],
        x: Symbol,
        bounds: Option<&(Expr, Expr)>,
    ) -> Result<Self, SolveError> {
        let (a, b) = bounds.cloned().unwrap_or_else(|| (-infinity(), infinity()));
        if depends(&a, x) || depends(&b, x) {
            return Err(error(format!("the bounds can't depend on `{}`", x.name())));
        }
        if infinity_sign(&a) == Some(Ordering::Greater) || infinity_sign(&b) == Some(Ordering::Less)
        {
            return Err(error("the lower bound must be below the upper bound"));
        }
        if has_step(f) {
            return Err(error("`floor`, `ceil` and `piecewise` aren't supported"));
        }
        let (lower, upper) = (finite(&a), finite(&b));
        if let (Some(a), Some(b)) = (lower, upper) {
            match compare(a, b) {
                Some(Ordering::Less) => {}
                Some(_) => return Err(error("the lower bound must be below the upper bound")),
                None => {
                    return Err(error(format!(
                        "can't check that `{}` is below `{}`",
                        plain(a),
                        plain(b)
                    )));
                }
            }
        }
        let derivative = f.derivative(x).normalize();
        let conditions = domain_conditions(f, domain, x);
        // Special points, where `f` may stop being defined or differentiable
        let mut special = vec![];
        for (u, _) in &conditions {
            special.extend(zeros(u, x)?);
        }
        let steps = step_arguments(f, x);
        for u in &steps {
            special.extend(zeros(u, x)?);
        }
        let (_, denominator) = derivative.as_fraction(true);
        if depends(&denominator, x) {
            special.extend(zeros(&denominator, x)?);
        }
        let parameters = |point: &Expr| parameters(f, point);
        let (special, special_families) = periodic(special, &parameters, lower, upper)?;
        if !special_families.is_empty() {
            return Err(error(
                "infinitely many points where the function isn't defined or differentiable",
            ));
        }
        // With `abs` or `sign`, critical points are found on each interval, where their signs are constant
        let (critical, families) = if steps.is_empty() {
            let equation = Equation::new(derivative.clone(), zero());
            let critical = roots(R.solve_for(&[equation], &[x])?, x)?;
            let (critical, families) = periodic(critical, &parameters, lower, upper)?;
            (critical, split_classes(f, x, families)?)
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
                "periodic critical points are only supported over ℝ for functions defined and differentiable \
                 everywhere",
            ));
        }
        // The open intervals between the points, kept when `f` is defined there
        let mut intervals: Vec<(Option<usize>, Option<usize>)> = vec![];
        if lower.is_none() {
            intervals.push((None, (!points.is_empty()).then_some(0)));
        }
        intervals.extend((1..points.len()).map(|i| (Some(i - 1), Some(i))));
        if upper.is_none() && !points.is_empty() {
            intervals.push((Some(points.len() - 1), None));
        }
        let end = |i: Option<usize>| i.map(|i| &points[i]);
        let mut pieces = vec![];
        for (i, j) in intervals {
            let (l, r) = (end(i), end(j));
            let at = sample((l, r));
            if !is_defined(&conditions, x, &at)? {
                continue;
            }
            let mut piece = Piece {
                lower: i,
                upper: j,
                derivative: derivative.clone(),
                critical: vec![],
                flat: false,
            };
            let critical = if steps.is_empty() {
                critical.clone()
            } else {
                let g = without_steps(f, x, &at)?;
                piece.derivative = g.derivative(x).normalize();
                if piece.derivative.expand().is_zero() {
                    piece.flat = true;
                    pieces.push(piece);
                    continue;
                }
                let equation = Equation::new(piece.derivative.clone(), zero());
                let critical = roots(R.solve_for(&[equation], &[x])?, x)?;
                let (critical, families) = periodic(critical, &parameters, l, r)?;
                if !families.is_empty() {
                    return Err(error(format!(
                        "periodic critical points of `{}` on an infinite interval",
                        plain(&g)
                    )));
                }
                critical
            };
            for point in critical {
                if is_inside(&point, l, r, true)? {
                    insert_sorted(&mut piece.critical, point)?;
                }
            }
            pieces.push(piece);
        }
        Ok(Self {
            f,
            x,
            lower: a,
            upper: b,
            conditions,
            points,
            pieces,
            families,
        })
    }

    /// The ends of `piece`, `None` being infinite.
    fn ends(&self, piece: &Piece) -> (Option<&Expr>, Option<&Expr>) {
        (
            piece.lower.map(|i| &self.points[i]),
            piece.upper.map(|i| &self.points[i]),
        )
    }

    /// The error for a function constant on `piece`.
    fn flat_error(&self, piece: &Piece) -> SolveError {
        let (l, r) = self.ends(piece);
        let end =
            |end: Option<&Expr>, infinite: &str| end.map_or_else(|| infinite.to_owned(), plain);
        error(format!(
            "the extremum is reached on the whole interval ({}, {})",
            end(l, "-oo"),
            end(r, "oo")
        ))
    }

    /// The text `the limit of f at point`, for errors.
    fn limit_text(&self, point: &Expr) -> String {
        format!("the limit of `{}` at `{}`", plain(self.f), plain(point))
    }

    /// Assume the integer parameters of `points` to be integers, until the returned guard is dropped.
    fn assume_integers<'p>(
        &self,
        points: impl IntoIterator<Item = &'p Expr>,
    ) -> Result<AssumptionsGuard, SolveError> {
        let mut assumptions = Assumptions::current();
        for point in points {
            for k in parameters(self.f, point) {
                assumptions.assume(k, Assumption::INTEGER).map_err(error)?;
            }
        }
        Ok(assumptions.enter())
    }

    /// The points where `f` reaches its global minimum.
    pub(super) fn global_min(&self) -> Result<Solution<Real>, SolveError> {
        let (f, x) = (self.f, self.x);
        // Limits at the ends of the intervals where `f` is defined, from inside
        let mut limits = vec![];
        for piece in &self.pieces {
            let (l, r) = self.ends(piece);
            limits.push(l.map_or_else(
                || (&self.lower, f.limit(x, &self.lower, Direction::Both)),
                |l| (l, f.limit(x, l, Direction::Right)),
            ));
            limits.push(r.map_or_else(
                || (&self.upper, f.limit(x, &self.upper, Direction::Both)),
                |r| (r, f.limit(x, r, Direction::Left)),
            ));
        }
        if limits
            .iter()
            .any(|(_, limit)| matches!(limit, Ok(l) if infinity_sign(l) == Some(Ordering::Less)))
        {
            return Ok(Solution::NoSolution);
        }
        // Candidates: special points where `f` is defined, critical points, and intervals where `f` is constant,
        // with a sample point
        let mut candidates: Vec<(Expr, Option<&Piece>)> = vec![];
        for point in &self.points {
            if is_defined(&self.conditions, x, point)? {
                candidates.push((point.clone(), None));
            }
        }
        for piece in &self.pieces {
            if piece.flat {
                candidates.push((sample(self.ends(piece)), Some(piece)));
            }
            candidates.extend(piece.critical.iter().map(|point| (point.clone(), None)));
        }
        let oscillating = !self.families.is_empty() && !self.pieces.is_empty();
        if oscillating {
            candidates.extend(self.families.iter().map(|point| (point.clone(), None)));
        }
        let _guard = self.assume_integers(candidates.iter().map(|(point, _)| point))?;
        let mut best = vec![];
        for (point, piece) in candidates {
            let value = subs(f, x, &point).expand();
            if has_special_constant(&value) {
                continue;
            }
            if let Some(k) = parameters(f, &point).first()
                && depends(&value, *k)
            {
                return Err(error(format!(
                    "the value `{}` at the periodic point `{}` depends on `{}`",
                    plain(&value),
                    plain(&point),
                    k.name()
                )));
            }
            keep_lowest(&mut best, (point, piece), value)?;
        }
        let Some((_, lowest)) = best.first() else {
            return Ok(Solution::NoSolution);
        };
        if let Some(((_, Some(piece)), _)) = best.iter().find(|((_, piece), _)| piece.is_some()) {
            return Err(self.flat_error(piece));
        }
        for (point, limit) in limits {
            let at = || self.limit_text(point);
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

    /// The points where `f` has a local minimum, relative to its domain.
    ///
    /// On each interval, the signs of the derivative between the sorted critical points give the critical points
    /// where it goes from negative to positive. At a special point where `f` is defined, `f` must be above its
    /// value on each side where it is defined: from the one-sided limit, or when it is equal to the value, from
    /// the sign of the derivative next to the point. Periodic critical points use the higher derivative test.
    pub(super) fn local_min(&self) -> Result<Solution<Real>, SolveError> {
        let (f, x) = (self.f, self.x);
        if let Some(piece) = self.pieces.iter().find(|piece| piece.flat) {
            return Err(self.flat_error(piece));
        }
        let mut minimizers = vec![];
        // For each point, whether the derivative next to it makes `f` go above its value, on each defined side
        let mut sides: Vec<Vec<(Direction, bool)>> = vec![vec![]; self.points.len()];
        // With periodic critical points there is a single interval, ℝ, whose critical points can't be sorted
        let pieces = if self.families.is_empty() {
            self.pieces.as_slice()
        } else {
            &[]
        };
        for piece in pieces {
            let (l, r) = self.ends(piece);
            let cuts: Vec<Option<&Expr>> = std::iter::once(l)
                .chain(piece.critical.iter().map(Some))
                .chain(std::iter::once(r))
                .collect();
            let mut signs = vec![];
            for cut in cuts.windows(2) {
                // Not zero between consecutive critical points, so its approximation decides, expanding only
                // when it fails (expanding at points made of nested radicals is slow)
                let at = subs(&piece.derivative, x, &sample((cut[0], cut[1])));
                let strict = |at: &Expr| {
                    constant_sign(at)
                        .filter(|sign| matches!(sign, Ordering::Less | Ordering::Greater))
                };
                let sign = strict(&at).or_else(|| strict(&at.expand()));
                signs.push(sign.ok_or_else(|| {
                    error(format!("can't find the sign of `{}`", plain(&at.expand())))
                })?);
            }
            for (i, point) in piece.critical.iter().enumerate() {
                if signs[i] == Ordering::Less && signs[i + 1] == Ordering::Greater {
                    minimizers.push(point.clone());
                }
            }
            if let Some(i) = piece.lower {
                sides[i].push((Direction::Right, signs[0] == Ordering::Greater));
            }
            if let Some(i) = piece.upper {
                sides[i].push((Direction::Left, signs[signs.len() - 1] == Ordering::Less));
            }
        }
        for (point, sides) in self.points.iter().zip(sides) {
            if sides.is_empty() || !is_defined(&self.conditions, x, point)? {
                continue;
            }
            let value = subs(f, x, point).expand();
            if has_special_constant(&value) {
                continue;
            }
            let mut above = true;
            for (direction, derivative_above) in sides {
                let limit = f
                    .limit(x, point, direction)
                    .map_err(|_| error(format!("can't find {}", self.limit_text(point))))?;
                above &= match infinity_sign(&limit) {
                    Some(sign) => sign == Ordering::Greater,
                    None if has_special_constant(&limit) => {
                        return Err(error(format!(
                            "can't decide {}, `{}`",
                            self.limit_text(point),
                            plain(&limit)
                        )));
                    }
                    None => match compare(&limit, &value) {
                        Some(Ordering::Greater) => true,
                        Some(Ordering::Less) => false,
                        Some(Ordering::Equal) => derivative_above,
                        None => {
                            return Err(error(format!(
                                "can't compare {} with `{}`",
                                self.limit_text(point),
                                plain(&value)
                            )));
                        }
                    },
                };
            }
            if above {
                minimizers.push(point.clone());
            }
        }
        if !self.pieces.is_empty() && !self.families.is_empty() {
            let _guard = self.assume_integers(&self.families)?;
            for point in &self.families {
                if self.is_min_by_derivatives(point)? {
                    minimizers.push(point.clone());
                }
            }
        }
        Ok(Solution::from_branches(
            minimizers
                .into_iter()
                .map(|point| vec![(x, point)])
                .collect(),
        ))
    }

    /// Whether `f` has a local minimum at the critical point `point`, by the first derivative of order at least 2
    /// not vanishing there: a minimum when its order is even and it is positive.
    fn is_min_by_derivatives(&self, point: &Expr) -> Result<bool, SolveError> {
        let mut derivative = self.f.derivative(self.x).normalize();
        for order in 2..=MAX_DERIVATIVE_ORDER {
            derivative = derivative.derivative(self.x).normalize();
            let at = subs(&derivative, self.x, point).expand();
            if at.is_zero() {
                continue;
            }
            if let Some(k) = parameters(self.f, point).first()
                && depends(&at, *k)
            {
                return Err(error(format!(
                    "the derivative `{}` at the periodic point `{}` depends on `{}`",
                    plain(&at),
                    plain(point),
                    k.name()
                )));
            }
            return match constant_sign(&at) {
                Some(Ordering::Equal) => continue,
                Some(sign) => Ok(order % 2 == 0 && sign == Ordering::Greater),
                None => Err(error(format!("can't find the sign of `{}`", plain(&at)))),
            };
        }
        Err(error(format!(
            "the derivatives of `{}` up to order {MAX_DERIVATIVE_ORDER} vanish at `{}`",
            plain(self.f),
            plain(point)
        )))
    }
}

/// The integer parameters of the periodic `point` which aren't symbols of `f`.
fn parameters(f: &Expr, point: &Expr) -> Vec<Symbol> {
    let used = f.symbols();
    point
        .symbols()
        .into_iter()
        .filter(|s| (is_integer_parameter(*s) || is_natural_parameter(*s)) && !used.contains(s))
        .collect()
}

/// The periodic points `families`, each `{$c(k)$}` split into the classes `{$c(m k + r)$}` of `k` modulo the
/// smallest `m` such that the value of `f` and its second derivative there don't depend on `k`, like `{$pi k$}` for
/// `{$cos x$}` into `{$2 pi k$}` and `{$pi + 2 pi k$}` (unsplit when there is none up to 4).
fn split_classes(f: &Expr, x: Symbol, families: Vec<Expr>) -> Result<Vec<Expr>, SolveError> {
    let second = f.derivative(x).normalize().derivative(x).normalize();
    let mut res = vec![];
    for point in families {
        let [k] = parameters(f, &point)[..] else {
            res.push(point);
            continue;
        };
        let mut assumptions = Assumptions::current();
        assumptions.assume(k, Assumption::INTEGER).map_err(error)?;
        let _guard = assumptions.enter();
        let constant = |point: &Expr| {
            [f, &second]
                .into_iter()
                .all(|g| !depends(&subs(g, x, point).expand(), k))
        };
        let classes = (1..=4).find_map(|m: i64| {
            let classes: Vec<Expr> = (0..m)
                .map(|r| {
                    let index = value(Rational::from(m)) * variable(k) + value(Rational::from(r));
                    subs(&point, k, &index).expand()
                })
                .collect();
            classes.iter().all(constant).then_some(classes)
        });
        match classes {
            Some(classes) => res.extend(classes),
            None => res.push(point),
        }
    }
    Ok(res)
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
pub fn has_step(term: &Expr) -> bool {
    has_function(term, &[Context::FLOOR, Context::CEIL, Context::PIECEWISE])
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
                for t in args {
                    walk(t, visit);
                }
            }
        }
    }
}

/// The conditions for `f` to be defined, with those of the terms of `domain` (see [`super::domain`]), each
/// once, those of subterms first.
pub(super) fn domain_conditions(f: &Expr, domain: &[Expr], x: Symbol) -> Vec<(Expr, Condition)> {
    let mut conditions = vec![];
    for term in domain.iter().chain([f]) {
        collect_conditions(term, x, false, &mut conditions);
    }
    let mut res: Vec<(Expr, Condition)> = vec![];
    for condition in conditions {
        if !res.contains(&condition) {
            res.push(condition);
        }
    }
    res
}

/// Push to `res` the conditions for `term` to be defined, those of its subterms first. Only those of parts
/// depending on `x`, unless `constants`, so that `{$sqrt(-1)$}` gives `{$-1 >= 0$}`.
pub fn collect_conditions(
    term: &Expr,
    x: Symbol,
    constants: bool,
    res: &mut Vec<(Expr, Condition)>,
) {
    if !constants && !depends(term, x) {
        return;
    }
    let recurse =
        |t: &Expr, res: &mut Vec<(Expr, Condition)>| collect_conditions(t, x, constants, res);
    match term {
        Term::Value(_) | Term::Symbol(_) => {}
        Term::Add(add) => add.iter().for_each(|t| recurse(t, res)),
        Term::Mul(mul) => mul.iter().for_each(|t| recurse(t, res)),
        Term::Pow(pow) => {
            recurse(&pow.base, res);
            recurse(&pow.exponant, res);
            let (base, exponent): (&Expr, &Expr) = (&pow.base, &pow.exponant);
            if !constants && !depends(base, x) {
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
                // Not for constant bases, like `{$(-1)^k$}` in a sum
                e if !is_integer(e) && depends(base, x) => {
                    res.push((base.clone(), Condition::Positive));
                }
                _ => {}
            }
        }
        Term::Fun(function) => {
            let Some(args) = function.get_args::<Real>() else {
                return;
            };
            for t in args {
                recurse(t, res);
            }
            let [u] = args.as_slice() else {
                return;
            };
            let square = || (one() - u.pow(&int(2))).normalize();
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
                // `{$-1/e <= u < 0$}`
                ident if ident == Context::lambertw_m1() => {
                    res.push((
                        (u.clone() + fun(Context::EXP, -one())).normalize(),
                        Condition::NonNegative,
                    ));
                    res.push(((-u.clone()).normalize(), Condition::Positive));
                }
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
