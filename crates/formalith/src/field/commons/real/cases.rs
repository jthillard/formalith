//! Case splits on the values of parameters.
//!
//! A calculus builtin (`lim`, `series`, `integrate`, `sum`, `product`) staying unevaluated because the sign of a
//! parameter, or of a linear form `{$k a + c$}` in a single parameter, is unknown is evaluated again on each side of
//! the points where the sign engine got stuck, the results being joined in a `piecewise`:
//! `{$integrate(sqrt(r/x - 1), x, 0, r) = (pi r)/2$}` without assumption on `r`, every branch agreeing, and
//! `{$lim(1/(a - 1)^n, n, oo)$}` is split at `{$a = 0, 1, 2$}`. The sign engine records the points of the symbols
//! whose sign it couldn't decide during the evaluation ([`record`]), the first of them (by name) among the parameters
//! of the call is split on, at most [`MAX_SPLIT_SYMBOLS`] of them in nested splits. The open intervals between the
//! points are assumed, the points are substituted; points recorded in a branch are added and the split done again,
//! up to [`MAX_SPLIT_POINTS`] of them. A branch still unevaluated keeps the call as its value.

use std::{
    cell::{Cell, RefCell},
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
};

use malachite::Rational;

use super::expr::{Expr, subs, value, variable};
use crate::{
    context::{
        Context, Symbol,
        assumptions::{
            Assumptions, SignSet,
            linear::{LinearForm, Var},
        },
    },
    term::{Expand, Fun, Term, flags::Flags, relation::Relation},
};

/// Number of parameters a call is split on at most, in nested splits.
pub const MAX_SPLIT_SYMBOLS: usize = 2;

/// Number of points a parameter is split at most at.
pub const MAX_SPLIT_POINTS: usize = 4;

/// Points of symbols at which their linear forms have an undecided sign.
type Points = BTreeMap<Symbol, BTreeSet<Rational>>;

thread_local! {
    /// The points recorded by the sign engine, while recording.
    static RECORDING: RefCell<Option<Points>> = const { RefCell::new(None) };
    /// Whether a split evaluation is running, builtins evaluated inside it don't split.
    static SPLITTING: Cell<bool> = const { Cell::new(false) };
}

/// Record that the sign of a linear form in `symbol` vanishing at `point` couldn't be decided, when recording.
pub fn record(symbol: Symbol, point: Rational) {
    RECORDING.with_borrow_mut(|recording| {
        if let Some(points) = recording {
            points.entry(symbol).or_default().insert(point);
        }
    });
}

/// `f()` without recording points, for signs of samples which say nothing about the parameters.
pub fn unrecorded<T>(f: impl FnOnce() -> T) -> T {
    let previous = RECORDING.take();
    let res = f();
    RECORDING.set(previous);
    res
}

/// Stops splitting, then recording, when dropped (also on panics).
struct Guard;

impl Drop for Guard {
    fn drop(&mut self) {
        RECORDING.with_borrow_mut(|current| *current = None);
        SPLITTING.set(false);
    }
}

/// Evaluate the call `ident(args)` with `eval` (`None` when it stays unevaluated), splitting on the values of its
/// parameters (`bound` being its variable) when it stays unevaluated.
pub fn evaluate(
    ident: Symbol,
    args: &[Expr],
    bound: Symbol,
    eval: &dyn Fn(&[Expr]) -> Option<Expr>,
) -> Option<Expr> {
    if SPLITTING.replace(true) {
        return eval(args);
    }
    let _guard = Guard;
    let call = Call { ident, bound, eval };
    call.split(args, MAX_SPLIT_SYMBOLS, &BTreeSet::new()).0
}

/// `eval(args)` and the points recorded during it. Evaluations of [`Call::split`] are sequential, so recordings
/// don't nest.
fn recorded(eval: &dyn Fn(&[Expr]) -> Option<Expr>, args: &[Expr]) -> (Option<Expr>, Points) {
    RECORDING.set(Some(Points::new()));
    let res = eval(args);
    let points = RECORDING.take().unwrap_or_default();
    (res, points)
}

/// Add to `symbols` the variables bound by the calculus builtins and held sums in `term`, like `k` in
/// `{$sum_(k = 0)^oo x^k$}`.
pub fn bound_symbols(term: &Expr, symbols: &mut BTreeSet<Symbol>) {
    match term {
        Term::Value(_) | Term::Symbol(_) => {}
        Term::Add(add) => add.iter().for_each(|t| bound_symbols(t, symbols)),
        Term::Mul(mul) => mul.iter().for_each(|t| bound_symbols(t, symbols)),
        Term::Pow(pow) => {
            bound_symbols(&pow.base, symbols);
            bound_symbols(&pow.exponant, symbols);
        }
        Term::Fun(fun) => {
            let Some(args) = fun.get_args::<super::Real>() else {
                return;
            };
            let ident = fun.get_ident();
            if (matches!(
                ident,
                Context::INTEGRATE
                    | Context::SUM
                    | Context::PRODUCT
                    | Context::LIM
                    | Context::SERIES
            ) || ident == Context::held_sum())
                && let Some(Term::Symbol(x)) = args.get(1)
            {
                symbols.insert(x.symbol);
            }
            for t in args {
                bound_symbols(t, symbols);
            }
        }
    }
}

/// The value of a branch, and whether it was evaluated.
type Branch = Option<(Expr, bool)>;

/// A call being split.
struct Call<'a> {
    ident: Symbol,
    bound: Symbol,
    eval: &'a dyn Fn(&[Expr]) -> Option<Expr>,
}

impl Call<'_> {
    /// The value of the call on `args`, split on at most `budget` parameters not in `excluded`, and the points
    /// recorded by its first evaluation.
    fn split(
        &self,
        args: &[Expr],
        budget: usize,
        excluded: &BTreeSet<Symbol>,
    ) -> (Option<Expr>, Points) {
        let (res, undecided) = recorded(self.eval, args);
        if res.is_some() || budget == 0 {
            return (res, undecided);
        }
        let (mut parameters, mut bound_inside) = (BTreeSet::new(), BTreeSet::new());
        for arg in args {
            arg.collect_symbols(&mut parameters);
            bound_symbols(arg, &mut bound_inside);
        }
        let mut candidates: Vec<Symbol> = undecided
            .keys()
            .copied()
            .filter(|s| {
                parameters.contains(s)
                    && *s != self.bound
                    && !excluded.contains(s)
                    && !bound_inside.contains(s)
                    && !Context::is_builtin_constant(*s)
                    && !s.name().starts_with('@')
            })
            .collect();
        candidates.sort_by_key(|s| s.name());
        let Some(&s) = candidates.first() else {
            return (None, undecided);
        };
        let mut excluded = excluded.clone();
        excluded.insert(s);
        let mut points = undecided[&s].clone();
        loop {
            let (branches, found) = self.branches(args, budget - 1, &excluded, s, &points);
            let all: BTreeSet<Rational> = points.union(&found).cloned().collect();
            if all.len() == points.len() || all.len() > MAX_SPLIT_POINTS {
                let evaluated = branches.iter().flatten().any(|(_, evaluated)| *evaluated);
                let points: Vec<Rational> = points.into_iter().collect();
                return (evaluated.then(|| join(s, &points, branches)), undecided);
            }
            points = all;
        }
    }

    /// The branches of the split of `s` at `points` (the intervals around the points, and the points), `None` for
    /// those excluded by the assumptions, and the new points of `s` recorded in the intervals.
    fn branches(
        &self,
        args: &[Expr],
        budget: usize,
        excluded: &BTreeSet<Symbol>,
        s: Symbol,
        points: &BTreeSet<Rational>,
    ) -> (Vec<Branch>, BTreeSet<Rational>) {
        let points: Vec<&Rational> = points.iter().collect();
        let mut found = BTreeSet::new();
        let mut res = vec![];
        let value_of = |res: Option<Expr>, args: Vec<Expr>| {
            let evaluated = res.is_some();
            // Its arguments are normalized, normalizing the held call would evaluate it again
            (
                res.unwrap_or_else(|| normalized_call(self.ident, args)),
                evaluated,
            )
        };
        for i in 0..=points.len() {
            let (lower, upper) = (i.checked_sub(1).map(|j| points[j]), points.get(i).copied());
            let mut assumptions = Assumptions::current();
            let feasible = lower.is_none_or(|c| {
                assumptions
                    .assume_relation(&offset(s, c), SignSet::POSITIVE)
                    .is_ok()
            }) && upper.is_none_or(|c| {
                assumptions
                    .assume_relation(&offset(s, c).neg(), SignSet::POSITIVE)
                    .is_ok()
            });
            res.push(feasible.then(|| {
                let _assumed = assumptions.enter();
                let (value, recorded) = self.split(args, budget, excluded);
                found.extend(
                    recorded
                        .get(&s)
                        .into_iter()
                        .flatten()
                        .filter(|p| lower.is_none_or(|c| *p > c) && upper.is_none_or(|c| *p < c))
                        .cloned(),
                );
                value_of(value, args.to_vec())
            }));
            if let Some(c) = upper {
                let possible = Assumptions::current()
                    .signs(&offset(s, c), &[])
                    .contains(Ordering::Equal);
                res.push(possible.then(|| {
                    let args: Vec<Expr> = args
                        .iter()
                        .map(|arg| subs(arg, s, &value(c.clone())))
                        .collect();
                    let (value, _) = self.split(&args, budget, excluded);
                    value_of(value, args)
                }));
            }
        }
        (res, found)
    }
}

/// `{$s - c$}`.
fn offset(s: Symbol, c: &Rational) -> LinearForm {
    LinearForm::variable(Var::Symbol(s)).add(&LinearForm::constant(-c))
}

/// The call `ident(args)` of normalized arguments, built without evaluating it.
pub fn normalized_call(ident: Symbol, args: Vec<Expr>) -> Expr {
    let mut res = Term::Fun(Box::new(Fun::new(ident, args, super::R)));
    res.set_normalized(true);
    res
}

/// Whether `a` and `b` are equal once expanded.
fn equal(a: &Expr, b: &Expr) -> bool {
    a == b || (a - b).expand().is_zero()
}

/// A branch of a `piecewise`: its condition `s relation c` (`None` for the default) and its value.
struct Entry {
    condition: Option<(Relation, Rational)>,
    value: Expr,
}

impl Entry {
    /// Whether the condition holds for every value above those of the previous conditions, up to its point.
    const fn covers_below(&self) -> bool {
        matches!(
            self.condition,
            None | Some((Relation::Less | Relation::LessEqual, _))
        )
    }
}

/// The `piecewise` of the branches of a split of `s` at `points` (see [`Call::branches`]), merged when they agree.
/// A point value isn't merged into a held call, which substituting `s` would evaluate.
fn join(s: Symbol, points: &[Rational], mut branches: Vec<Branch>) -> Expr {
    let mut less_equal = vec![false; points.len() + 1];
    // Points merged into a neighboring interval, the right one first
    for (k, c) in points.iter().enumerate() {
        let Some((z, _)) = &branches[2 * k + 1] else {
            continue;
        };
        let agrees = |side: &Branch| {
            side.as_ref().is_some_and(|(value, evaluated)| {
                *evaluated && equal(&subs(value, s, &super::expr::value(c.clone())), z)
            })
        };
        if agrees(&branches[2 * k + 2]) {
            branches[2 * k + 1] = None;
        } else if agrees(&branches[2 * k]) {
            branches[2 * k + 1] = None;
            less_equal[k] = true;
        }
    }
    let mut entries: Vec<Entry> = branches
        .into_iter()
        .enumerate()
        .filter_map(|(i, branch)| {
            let (value, _) = branch?;
            let condition = if i % 2 == 1 {
                Some((Relation::Equal, points[i / 2].clone()))
            } else {
                points.get(i / 2).map(|c| {
                    let relation = if less_equal[i / 2] {
                        Relation::LessEqual
                    } else {
                        Relation::Less
                    };
                    (relation, c.clone())
                })
            };
            Some(Entry { condition, value })
        })
        .collect();
    if let Some(last) = entries.last_mut() {
        last.condition = None;
    }
    // Consecutive agreeing branches merged
    let mut changed = true;
    while changed {
        changed = false;
        for i in 0..entries.len().saturating_sub(1) {
            let (a, b) = (&entries[i], &entries[i + 1]);
            let point_after_interval = matches!(
                (&a.condition, &b.condition),
                (Some((Relation::Less, c)), Some((Relation::Equal, d))) if c == d
            );
            if equal(&a.value, &b.value) && (b.covers_below() || point_after_interval) {
                if point_after_interval {
                    entries[i + 1].condition = entries[i]
                        .condition
                        .take()
                        .map(|(_, c)| (Relation::LessEqual, c));
                }
                entries.remove(i);
                changed = true;
                break;
            }
            // A point between two agreeing branches goes first: `{$s = c$}` then the rest
            if point_after_interval
                && entries
                    .get(i + 2)
                    .is_some_and(|next| next.covers_below() && equal(&a.value, &next.value))
            {
                entries.swap(i, i + 1);
                changed = true;
                break;
            }
        }
    }
    if entries.len() == 1 {
        return entries.remove(0).value;
    }
    let mut args = vec![];
    for entry in entries {
        if let Some((relation, c)) = entry.condition {
            args.push(normalized_call(
                relation.symbol(),
                vec![variable(s), value(c)],
            ));
        }
        args.push(entry.value);
    }
    super::R
        .eval_piecewise(&args)
        .unwrap_or_else(|| normalized_call(Context::PIECEWISE, args))
}
