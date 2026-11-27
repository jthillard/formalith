//! Case splits on the values of parameters.
//!
//! A calculus builtin (`lim`, `series`, `integrate`, `sum`, `product`) staying unevaluated because the sign of a
//! parameter, or of a linear form `{$k a + c$}` in parameters, is unknown is evaluated again on each side of the
//! points where the sign engine got stuck, the results being joined in a `piecewise`:
//! `{$integrate(sqrt(r/x - 1), x, 0, r) = (pi r)/2$}` without assumption on `r`, every branch agreeing, and
//! `{$lim(1/(a - 1)^n, n, oo)$}` is split at `{$a = 0, 1, 2$}`. The sign engine records the values of the linear
//! forms (without constant) whose sign it couldn't decide during the evaluation ([`record`], [`record_form`]), the
//! first of them among the parameters of the call is split on (single symbols by name first, then relations between
//! several of them, like `{$x - r_1$}` for `{$integrate(sqrt(x/r - 1), r, r_1, x)$}`), at most [`MAX_SPLITS`] of them
//! in nested splits. The open intervals between the points are assumed, the points are substituted (solved for the
//! first symbol of the form by name); points recorded in a branch are added and the split done again, up to
//! [`MAX_SPLIT_POINTS`] of them. A branch still unevaluated keeps the call as its value.

use std::{
    cell::{Cell, RefCell},
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
};

use malachite::{
    Rational,
    base::num::{
        arithmetic::traits::Reciprocal,
        basic::traits::{One, Zero},
    },
};

use super::{
    expr::{Expr, depends, subs, value, variable},
    sign::linear_expr,
};
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

/// Number of linear forms (parameters or relations between them) a call is split on at most, in nested splits.
pub const MAX_SPLITS: usize = 3;

/// Number of points a linear form is split at most at.
pub const MAX_SPLIT_POINTS: usize = 4;

/// Values of linear forms in symbols (without constant, primitive with a positive first coefficient) at which a form
/// had an undecided sign.
type Points = BTreeMap<LinearForm, BTreeSet<Rational>>;

thread_local! {
    /// The points recorded by the sign engine, while recording.
    static RECORDING: RefCell<Option<Points>> = const { RefCell::new(None) };
    /// Whether a split evaluation is running, builtins evaluated inside it don't split.
    static SPLITTING: Cell<bool> = const { Cell::new(false) };
}

/// Record that the sign of a linear form in `symbol` vanishing at `point` couldn't be decided, when recording.
pub fn record(symbol: Symbol, point: Rational) {
    insert(LinearForm::variable(Var::Symbol(symbol)), point);
}

/// Record that the sign of `form`, a linear form in symbols, couldn't be decided, when recording. Forms with other
/// variables or without symbol are ignored.
pub fn record_form(form: &LinearForm) {
    let Some(first) = form.coefficients.values().next() else {
        return;
    };
    if form.coefficients.keys().any(|x| matches!(x, Var::Atom(_))) {
        return;
    }
    let homogeneous = LinearForm {
        coefficients: form.coefficients.clone(),
        constant: Rational::ZERO,
    };
    let key = homogeneous.primitive();
    let mut scale = key
        .coefficients
        .values()
        .next()
        .map_or(Rational::ONE, |c| c / first);
    if *first < 0 {
        scale = -scale;
    }
    insert(homogeneous.scale(&scale), -(&form.constant * scale));
}

fn insert(form: LinearForm, point: Rational) {
    RECORDING.with_borrow_mut(|recording| {
        if let Some(points) = recording {
            points.entry(form).or_default().insert(point);
        }
    });
}

/// `f()` without recording points, for signs of samples which say nothing about the parameters.
pub fn unrecorded<T>(f: impl FnOnce() -> T) -> T {
    /// Restores the points recorded before when dropped (also on panics).
    struct Restore(Option<Points>);
    impl Drop for Restore {
        fn drop(&mut self) {
            RECORDING.set(self.0.take());
        }
    }
    let _restore = Restore(RECORDING.take());
    f()
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
    // A bound depending on the variable makes it a parameter too, so the variable is renamed:
    // `{$integral_0^x cos(sqrt(x)) dif x = integral_0^x cos(sqrt(t)) dif t$}`
    if matches!(ident, Context::INTEGRATE | Context::SUM | Context::PRODUCT)
        && let [f, _, a, b] = args
        && (depends(a, bound) || depends(b, bound))
    {
        let dummy = Symbol::new("@c");
        let args = [
            subs(f, bound, &variable(dummy)),
            variable(dummy),
            a.clone(),
            b.clone(),
        ];
        let call = Call {
            ident,
            bound: dummy,
            eval,
        };
        return call.split(&args, MAX_SPLITS, &BTreeSet::new()).0;
    }
    let call = Call { ident, bound, eval };
    call.split(args, MAX_SPLITS, &BTreeSet::new()).0
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
    /// The value of the call on `args`, split on at most `budget` linear forms not in `excluded`, and the points
    /// recorded by its first evaluation.
    fn split(
        &self,
        args: &[Expr],
        budget: usize,
        excluded: &BTreeSet<LinearForm>,
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
        let is_parameter = |s: &Symbol| {
            parameters.contains(s)
                && *s != self.bound
                && !bound_inside.contains(s)
                && !Context::is_builtin_constant(*s)
                && !s.name().starts_with('@')
        };
        let mut candidates: Vec<Split> = undecided
            .keys()
            .filter(|form| !excluded.contains(*form) && form.symbols().all(|s| is_parameter(&s)))
            .filter_map(Split::new)
            .collect();
        candidates.sort_by_key(|split| {
            let mut names: Vec<&str> = split.form.symbols().map(Symbol::name).collect();
            names.sort_unstable();
            (names.len(), names)
        });
        let Some(split) = candidates.into_iter().next() else {
            return (None, undecided);
        };
        let mut excluded = excluded.clone();
        excluded.insert(split.form.clone());
        let mut points = undecided[&split.form].clone();
        loop {
            let (branches, found) = self.branches(args, budget - 1, &excluded, &split, &points);
            let all: BTreeSet<Rational> = points.union(&found).cloned().collect();
            if all.len() == points.len() || all.len() > MAX_SPLIT_POINTS {
                let evaluated = branches.iter().flatten().any(|(_, evaluated)| *evaluated);
                let points: Vec<Rational> = points.into_iter().collect();
                return (
                    evaluated.then(|| join(&split, &points, branches)),
                    undecided,
                );
            }
            points = all;
        }
    }

    /// The branches of the split of a form at `points` (the intervals around the points, and the points), `None`
    /// for those excluded by the assumptions, and the new points of the form recorded in the intervals.
    fn branches(
        &self,
        args: &[Expr],
        budget: usize,
        excluded: &BTreeSet<LinearForm>,
        split: &Split,
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
                    .assume_relation(&split.offset(c), SignSet::POSITIVE)
                    .is_ok()
            }) && upper.is_none_or(|c| {
                assumptions
                    .assume_relation(&split.offset(c).neg(), SignSet::POSITIVE)
                    .is_ok()
            });
            res.push(feasible.then(|| {
                let _assumed = assumptions.enter();
                let (value, recorded) = self.split(args, budget, excluded);
                found.extend(
                    recorded
                        .get(&split.form)
                        .into_iter()
                        .flatten()
                        .filter(|p| lower.is_none_or(|c| *p > c) && upper.is_none_or(|c| *p < c))
                        .cloned(),
                );
                value_of(value, args.to_vec())
            }));
            if let Some(c) = upper {
                let possible = Assumptions::current()
                    .signs(&split.offset(c), &[])
                    .contains(Ordering::Equal);
                res.push(possible.then(|| {
                    let args: Vec<Expr> = args.iter().map(|arg| split.at(arg, c)).collect();
                    let (value, _) = self.split(&args, budget, excluded);
                    value_of(value, args)
                }));
            }
        }
        (res, found)
    }
}

/// A linear form being split on, solved for its first symbol by name `s` at the points.
struct Split {
    form: LinearForm,
    s: Symbol,
}

impl Split {
    fn new(form: &LinearForm) -> Option<Self> {
        let s = form.symbols().min_by_key(|s| s.name())?;
        Some(Self {
            form: form.clone(),
            s,
        })
    }

    /// `{$f - c$}`.
    fn offset(&self, c: &Rational) -> LinearForm {
        self.form.add(&LinearForm::constant(-c))
    }

    /// `term` where the form is `c`, `s` being substituted.
    fn at(&self, term: &Expr, c: &Rational) -> Expr {
        let k = self.form.coefficient(Var::Symbol(self.s));
        let mut rest = self.offset(c);
        rest.coefficients.remove(&Var::Symbol(self.s));
        let solved = linear_expr(&rest.scale(&-k.reciprocal()), &[]);
        subs(term, self.s, &solved)
    }

    /// The condition `{$f relation c$}`, with the terms of negative coefficients on the right, like `{$x < r_1$}`.
    fn condition(&self, relation: Relation, c: &Rational) -> Expr {
        let (mut lhs, mut rhs) = (value(Rational::ZERO), value(c.clone()));
        for (x, k) in &self.form.coefficients {
            let Var::Symbol(x) = x else { continue };
            if *k > 0 {
                lhs += value(k.clone()) * variable(*x);
            } else {
                rhs += value(-k) * variable(*x);
            }
        }
        normalized_call(relation.symbol(), vec![lhs, rhs])
    }
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

/// A branch of a `piecewise`: its condition `f relation c` (`None` for the default) and its value.
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

/// The `piecewise` of the branches of a split at `points` (see [`Call::branches`]), merged when they agree. A point
/// value isn't merged into a held call, which substituting would evaluate.
fn join(split: &Split, points: &[Rational], mut branches: Vec<Branch>) -> Expr {
    let mut less_equal = vec![false; points.len() + 1];
    // Points merged into a neighboring interval, the right one first
    for (k, c) in points.iter().enumerate() {
        let Some((z, _)) = &branches[2 * k + 1] else {
            continue;
        };
        let agrees = |side: &Branch| {
            side.as_ref()
                .is_some_and(|(value, evaluated)| *evaluated && equal(&split.at(value, c), z))
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
            args.push(split.condition(relation, &c));
        }
        args.push(entry.value);
    }
    super::R
        .eval_piecewise(&args)
        .unwrap_or_else(|| normalized_call(Context::PIECEWISE, args))
}
