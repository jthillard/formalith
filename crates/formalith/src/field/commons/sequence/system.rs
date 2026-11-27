//! Sequences as systems of recurrences, the elements of [`super::Seq`].
//!
//! A sequence is the last of a list of equations `{$u_j (n) = "rule"_j$}`, each rule being an expression in the
//! index `n` and in the earlier sequences at `{$n - d$}` (`{$d >= 0$}`) or in its own sequence at `{$n - d$}`
//! (`{$d >= 1$}`, a recurrence, its order being the largest such `d`). A recurrence of order `r` starts at an index
//! `{$n_0$}` with the initial values `{$u(n_0), ..., u(n_0 + r - 1)$}`, and an equation may have values replacing its
//! rule at some indices. A closed form is a single equation of order 0 without references, its general term.
//!
//! Every operation is componentwise, appending an equation to the merged systems, then the system is made canonical
//! (equations of order 0 inlined in the next ones, unused and repeated equations removed), so that operations on
//! closed forms stay closed forms and `{$u - u = 0$}`.

// Indices and orders are small
#![allow(
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_possible_truncation
)]

use std::{
    collections::{HashMap, VecDeque},
    rc::Rc,
};

use crate::{
    context::Symbol,
    term::{Expand, Fun, Normalize, SymbolTerm, Term},
};

use super::{Seq, SequenceValues};

/// Largest number of terms computed when iterating a system, beyond which a term stays unevaluated.
pub const MAX_SEQUENCE_STEPS: i64 = 100_000;
/// Largest shift `{$u(n + k)$}` written with the rules of the recurrences of `u`, larger ones shifting their
/// starts.
const MAX_UNFOLD: i64 = 256;
/// Largest size of a rule written for a shift, beyond which the starts are shifted.
const MAX_UNFOLD_SIZE: usize = 200;
/// Largest number of first indices whose values are computed where an unfolded shift doesn't hold.
const MAX_UNFOLD_EXCEPTIONS: i64 = 64;
/// Largest number of passes making a system canonical.
const MAX_PASSES: usize = 16;

/// A reference, in a rule, to a sequence of the system at `{$n - d$}`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ref {
    /// The sequence of the equation, `{$d >= 1$}`.
    Own(usize),
    /// The sequence of the equation `j`, an earlier one.
    Other(usize, usize),
}

impl Ref {
    /// The internal symbol standing for the reference in a rule, `@r{d}` or `@s{j}_{d}`.
    pub(crate) fn symbol(self) -> Symbol {
        Symbol::new(match self {
            Self::Own(d) => format!("@r{d}"),
            Self::Other(j, d) => format!("@s{j}_{d}"),
        })
    }

    /// The reference of an internal symbol.
    pub(crate) fn parse(symbol: Symbol) -> Option<Self> {
        let name = symbol.name();
        if let Some(d) = name.strip_prefix("@r") {
            return d.parse().ok().map(Self::Own);
        }
        let (j, d) = name.strip_prefix("@s")?.split_once('_')?;
        Some(Self::Other(j.parse().ok()?, d.parse().ok()?))
    }

    /// The shift `d`.
    const fn delay(self) -> usize {
        match self {
            Self::Own(d) | Self::Other(_, d) => d,
        }
    }

    /// The reference as a term.
    pub(crate) fn term<K: SequenceValues>(self, set: K) -> Term<K> {
        Term::Symbol(SymbolTerm::new(self.symbol(), set))
    }
}

/// Rebuild `term`, replacing each node for which `f` returns a term, normalizing the result. Functions whose
/// arguments live in another set are kept.
pub fn rewrite<K: SequenceValues>(
    term: &Term<K>,
    f: &mut dyn FnMut(&Term<K>) -> Option<Term<K>>,
) -> Term<K> {
    if let Some(res) = f(term) {
        return res;
    }
    let set = term.get_set();
    match term {
        Term::Value(_) | Term::Symbol(_) => term.clone(),
        Term::Add(add) => add
            .iter()
            .fold(Term::zero(set), |res, t| res + rewrite(t, f)),
        Term::Mul(mul) => mul
            .iter()
            .fold(Term::constant(mul.coefficient.clone(), set), |res, t| {
                res * rewrite(t, f)
            }),
        Term::Pow(pow) => rewrite(&pow.base, f).pow(&rewrite(&pow.exponant, f)),
        Term::Fun(fun) => fun.get_args::<K>().map_or_else(
            || term.clone(),
            |args| {
                let args = args.iter().map(|arg| rewrite(arg, f)).collect();
                Term::Fun(Box::new(Fun::new(fun.get_ident(), args, set))).normalize()
            },
        ),
    }
}

/// Replace the symbol `symbol` by `value` in `term`, exponents and function arguments included.
pub fn substitute<K: SequenceValues>(term: &Term<K>, symbol: Symbol, value: &Term<K>) -> Term<K> {
    if !term.symbols().contains(&symbol) {
        return term.clone();
    }
    rewrite(term, &mut |t| match t {
        Term::Symbol(s) if s.symbol == symbol => Some(value.clone()),
        _ => None,
    })
}

/// The references of `term`.
fn refs<K: SequenceValues>(term: &Term<K>) -> Vec<Ref> {
    term.symbols().into_iter().filter_map(Ref::parse).collect()
}

/// An equation `{$u(n) = "rule"$}` of a system, see the [module documentation](self).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Equation<K: SequenceValues> {
    /// The index of the first initial value, for a recurrence.
    pub(crate) start: i64,
    /// The initial values, as many as the order.
    pub(crate) initial: Vec<Term<K>>,
    /// The values replacing the rule, by increasing index.
    pub(crate) overrides: Vec<(i64, Term<K>)>,
    /// The general term, with references.
    pub(crate) rule: Term<K>,
}

impl<K: SequenceValues> Equation<K> {
    /// The equation of the closed form `rule`.
    pub(crate) const fn closed(rule: Term<K>) -> Self {
        Self {
            start: 0,
            initial: vec![],
            overrides: vec![],
            rule,
        }
    }

    /// The order, the largest shift of a reference to its own sequence.
    pub(crate) fn order(&self) -> usize {
        refs(&self.rule)
            .into_iter()
            .filter_map(|r| match r {
                Ref::Own(d) => Some(d),
                Ref::Other(..) => None,
            })
            .max()
            .unwrap_or(0)
    }

    /// The value given at `n`, an initial value or an override, `None` if the rule gives it.
    fn given(&self, n: i64, order: usize) -> Option<&Term<K>> {
        if order > 0 && (self.start..self.start + order as i64).contains(&n) {
            return self.initial.get((n - self.start) as usize);
        }
        self.overrides
            .iter()
            .find(|(index, _)| *index == n)
            .map(|(_, value)| value)
    }

    /// Rename the references to other equations, `None` keeping them.
    fn rename(&self, f: &dyn Fn(usize, usize) -> Option<Term<K>>) -> Self {
        let rule = rewrite(&self.rule, &mut |t| match t {
            Term::Symbol(s) => match Ref::parse(s.symbol) {
                Some(Ref::Other(j, d)) => f(j, d),
                _ => None,
            },
            _ => None,
        });
        Self {
            rule,
            ..self.clone()
        }
    }
}

/// A sequence, the last equation of a system, see the [module documentation](self).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Sequence<K: SequenceValues> {
    pub(crate) equations: Rc<[Equation<K>]>,
}

impl<K: SequenceValues> Sequence<K> {
    /// The sequence of general term `rule`.
    #[must_use]
    pub fn closed(rule: Term<K>) -> Self {
        Self {
            equations: Rc::new([Equation::closed(rule)]),
        }
    }

    /// The general term of a closed form, `None` for a recurrence.
    #[must_use]
    pub fn as_closed(&self) -> Option<&Term<K>> {
        match &*self.equations {
            [equation] if equation.overrides.is_empty() && refs(&equation.rule).is_empty() => {
                Some(&equation.rule)
            }
            _ => None,
        }
    }

    /// The equations of the system, the last one being the sequence.
    #[must_use]
    pub fn equations(&self) -> &[Equation<K>] {
        &self.equations
    }

    /// The canonical sequence of a system, see the [module documentation](self).
    pub(crate) fn from_equations(mut equations: Vec<Equation<K>>, set: Seq<K>) -> Self {
        for _ in 0..MAX_PASSES {
            let before = equations.clone();
            demote_initial_values(&mut equations, set);
            cancel_references(&mut equations);
            inline(&mut equations, set);
            alias(&mut equations);
            equations = prune(equations);
            equations = dedupe(equations);
            if equations == before {
                break;
            }
        }
        if let [equation] = equations.as_mut_slice()
            && equation.order() == 0
        {
            equation.start = 0;
            equation.initial.clear();
        }
        Self {
            equations: equations.into(),
        }
    }

    /// The sequence `{$f(u_1, ..., u_k)$}`, `f` being applied to the general terms.
    pub(crate) fn map(
        args: &[&Self],
        set: Seq<K>,
        f: impl FnOnce(Vec<Term<K>>) -> Term<K>,
    ) -> Self {
        if let Some(rules) = args
            .iter()
            .map(|arg| arg.as_closed().cloned())
            .collect::<Option<Vec<_>>>()
        {
            return Self::closed(f(rules));
        }
        let mut equations: Vec<Equation<K>> = vec![];
        let mut lasts = vec![];
        for arg in args {
            let offset = equations.len();
            equations.extend(arg.equations.iter().map(|equation| {
                equation.rename(&|j, d| Some(Ref::Other(j + offset, d).term(set.values)))
            }));
            lasts.push(Ref::Other(equations.len() - 1, 0).term(set.values));
        }
        equations.push(Equation::closed(f(lasts)));
        Self::from_equations(equations, set)
    }

    /// The sequence with `f` applied to its rules, like an expansion.
    pub(crate) fn map_rules(&self, set: Seq<K>, f: impl Fn(&Term<K>) -> Term<K>) -> Self {
        let equations = self
            .equations
            .iter()
            .map(|equation| Equation {
                rule: f(&equation.rule),
                ..equation.clone()
            })
            .collect();
        Self::from_equations(equations, set)
    }

    /// The term of index `m`, `None` if it isn't defined or can't be computed (too many terms, a value missing).
    #[must_use]
    pub fn at(&self, set: Seq<K>, m: i64) -> Option<Term<K>> {
        let index = Term::nth(m, set.values);
        if let Some(rule) = self.as_closed() {
            return Some(substitute(rule, set.index, &index));
        }
        let equations = &self.equations;
        let orders: Vec<usize> = equations.iter().map(Equation::order).collect();
        let delay = equations
            .iter()
            .flat_map(|equation| refs(&equation.rule))
            .map(Ref::delay)
            .max()
            .unwrap_or(0);
        let history = delay * equations.len();
        let low = equations
            .iter()
            .zip(&orders)
            .filter(|(_, order)| **order > 0)
            .map(|(equation, _)| equation.start)
            .min()
            .map_or(m - history as i64, |start| start.min(m - history as i64));
        if m - low > MAX_SEQUENCE_STEPS {
            return None;
        }
        // The last values of each equation, from `{$n - "delay"$}` to `n`
        let mut windows: Vec<VecDeque<Option<Term<K>>>> = vec![VecDeque::new(); equations.len()];
        for n in low..=m {
            for (j, (equation, &order)) in equations.iter().zip(&orders).enumerate() {
                let value = match equation.given(n, order) {
                    Some(value) => Some(value.clone()),
                    None if order > 0 && n < equation.start => None,
                    None => eval_rule(&equation.rule, j, n, &windows, set),
                };
                let window = &mut windows[j];
                window.push_back(value);
                if window.len() > delay + 1 {
                    window.pop_front();
                }
            }
        }
        windows.last()?.back()?.clone()
    }

    /// The sequence `{$u(n + k)$}`.
    #[must_use]
    pub fn shift(&self, set: Seq<K>, k: i64) -> Self {
        if k == 0 {
            return self.clone();
        }
        let index = Term::Symbol(SymbolTerm::new(set.index, set.values));
        let shifted_index = index + Term::nth(k, set.values);
        if let Some(rule) = self.as_closed() {
            return Self::closed(substitute(rule, set.index, &shifted_index));
        }
        let last = self.equations.len() - 1;
        if k < 0 {
            let mut equations = self.equations.to_vec();
            equations.push(Equation::closed(
                Ref::Other(last, k.unsigned_abs() as usize).term(set.values),
            ));
            return Self::from_equations(equations, set);
        }
        if k <= MAX_UNFOLD
            && let Some(unfolded) = self.unfold(set, k)
        {
            return unfolded;
        }
        // Every equation is shifted, the references being relative
        let equations = self
            .equations
            .iter()
            .map(|equation| Equation {
                start: equation.start - k,
                initial: equation.initial.clone(),
                overrides: equation
                    .overrides
                    .iter()
                    .map(|(n, value)| (n - k, value.clone()))
                    .collect(),
                rule: substitute(&equation.rule, set.index, &shifted_index),
            })
            .collect();
        Self::from_equations(equations, set)
    }

    /// `{$u(n + k)$}` written with the rules of the system, as a new equation referring to the others: `{$u(n + 1) =
    /// 2 u(n) + 1$}` for `{$u(n) = 2 u(n - 1) + 1$}`. `None` when the system has overrides, or when the rules don't
    /// hold at too many first indices.
    fn unfold(&self, set: Seq<K>, k: i64) -> Option<Self> {
        if self.equations.iter().any(|e| !e.overrides.is_empty()) {
            return None;
        }
        let last = self.equations.len() - 1;
        let mut memo = HashMap::new();
        let (rule, threshold) = self.forward(set, last, k as usize, &mut memo)?;
        if threshold > MAX_UNFOLD_EXCEPTIONS {
            return None;
        }
        let mut overrides = vec![];
        for n in 0..threshold {
            overrides.push((n, self.at(set, n + k)?));
        }
        let mut equations = self.equations.to_vec();
        equations.push(Equation {
            start: 0,
            initial: vec![],
            overrides,
            rule,
        });
        Some(Self::from_equations(equations, set))
    }

    /// The rule of the equation `j` at `{$n + e$}` (`{$e >= 1$}`), expanded, with references at `{$n - d$}` for
    /// `{$d >= 0$}`, and the least `n` from which it holds. `None` when it grows beyond [`MAX_UNFOLD_SIZE`].
    fn forward(
        &self,
        set: Seq<K>,
        j: usize,
        e: usize,
        memo: &mut HashMap<(usize, usize), (Term<K>, i64)>,
    ) -> Option<(Term<K>, i64)> {
        if let Some(res) = memo.get(&(j, e)) {
            return Some(res.clone());
        }
        let equation = &self.equations[j];
        let order = equation.order();
        let mut threshold = if order > 0 {
            equation.start + order as i64 - e as i64
        } else {
            i64::MIN
        };
        let index = Term::Symbol(SymbolTerm::new(set.index, set.values));
        let shifted = index + Term::nth(e as i64, set.values);
        let mut failed = false;
        let rule = rewrite(&equation.rule, &mut |t| {
            let Term::Symbol(s) = t else { return None };
            if s.symbol == set.index {
                return Some(shifted.clone());
            }
            let (i, d) = match Ref::parse(s.symbol)? {
                Ref::Own(d) => (j, d),
                Ref::Other(i, d) => (i, d),
            };
            if d >= e {
                return Some(Ref::Other(i, d - e).term(set.values));
            }
            let Some((term, from)) = (!failed)
                .then(|| self.forward(set, i, e - d, memo))
                .flatten()
            else {
                failed = true;
                return Some(Term::zero(set.values));
            };
            threshold = threshold.max(from);
            Some(term)
        });
        if failed {
            return None;
        }
        let rule = rule.expand();
        if size(&rule) > MAX_UNFOLD_SIZE {
            return None;
        }
        memo.insert((j, e), (rule.clone(), threshold));
        Some((rule, threshold))
    }
}

/// The rule of the equation `j` at `n`, the values of the equations at `{$n - d$}` being the last of `windows`
/// (their value at `n` for the earlier equations), `None` when one is missing.
fn eval_rule<K: SequenceValues>(
    rule: &Term<K>,
    j: usize,
    n: i64,
    windows: &[VecDeque<Option<Term<K>>>],
    set: Seq<K>,
) -> Option<Term<K>> {
    let mut missing = false;
    let n_term = Term::nth(n, set.values);
    let value = rewrite(rule, &mut |t| {
        let Term::Symbol(s) = t else { return None };
        if s.symbol == set.index {
            return Some(n_term.clone());
        }
        let (window, back) = match Ref::parse(s.symbol)? {
            // Its value at `n` isn't in its window yet
            Ref::Own(d) => (&windows[j], d),
            Ref::Other(i, d) => (&windows[i], d + 1),
        };
        let value = window
            .len()
            .checked_sub(back)
            .and_then(|position| window[position].clone());
        if value.is_none() {
            missing = true;
        }
        Some(value.unwrap_or_else(|| Term::zero(set.values)))
    });
    (!missing).then_some(value)
}

/// The number of nodes of `term`.
fn size<K: SequenceValues>(term: &Term<K>) -> usize {
    1 + match term {
        Term::Value(_) | Term::Symbol(_) => 0,
        Term::Add(add) => add.iter().map(size).sum(),
        Term::Mul(mul) => mul.iter().map(size).sum(),
        Term::Pow(pow) => size(&pow.base) + size(&pow.exponant),
        Term::Fun(fun) => fun
            .get_args::<K>()
            .map_or(1, |args| args.iter().map(size).sum()),
    }
}

/// The initial values of recurrences whose order decreased become overrides, and overrides of closed forms equal to
/// their general term are dropped.
fn demote_initial_values<K: SequenceValues>(equations: &mut [Equation<K>], set: Seq<K>) {
    for equation in equations {
        let order = equation.order();
        if equation.initial.len() > order {
            let start = equation.start;
            for (i, value) in equation.initial.drain(order..).enumerate() {
                let n = start + (order + i) as i64;
                if !equation.overrides.iter().any(|(index, _)| *index == n) {
                    equation.overrides.push((n, value));
                }
            }
            equation.overrides.sort_by_key(|(n, _)| *n);
        }
        if order == 0 && refs(&equation.rule).is_empty() {
            let rule = &equation.rule;
            equation.overrides.retain(|(n, value)| {
                let general = substitute(rule, set.index, &Term::nth(*n, set.values));
                let difference = &general - value;
                !(difference.is_zero() || difference.expand().is_zero())
            });
        }
    }
}

/// Expand the rules where it removes references, like `{$-(u(n) + v(n)) + u(n) + v(n) = 0$}`.
fn cancel_references<K: SequenceValues>(equations: &mut [Equation<K>]) {
    for equation in equations {
        let count = refs(&equation.rule).len();
        if count == 0 {
            continue;
        }
        let expanded = equation.rule.expand();
        if refs(&expanded).len() < count {
            equation.rule = expanded;
        }
    }
}

/// Inline the equations of order 0, except the last one, in the next rules. Where an inlined equation has a value
/// replacing its rule, the equation it is inlined in gets its value computed there.
fn inline<K: SequenceValues>(equations: &mut [Equation<K>], set: Seq<K>) {
    let index = Term::Symbol(SymbolTerm::new(set.index, set.values));
    for j in 0..equations.len().saturating_sub(1) {
        if equations[j].order() != 0 {
            continue;
        }
        let rule = equations[j].rule.clone();
        let exceptions: Vec<i64> = equations[j].overrides.iter().map(|(n, _)| *n).collect();
        // The rule at `{$n - d$}`
        let at = |d: usize| {
            if d == 0 {
                return rule.clone();
            }
            let shifted = index.clone() - Term::nth(d as i64, set.values);
            rewrite(&rule, &mut |t| {
                let Term::Symbol(s) = t else { return None };
                if s.symbol == set.index {
                    return Some(shifted.clone());
                }
                match Ref::parse(s.symbol)? {
                    Ref::Other(i, e) => Some(Ref::Other(i, e + d).term(set.values)),
                    Ref::Own(_) => None,
                }
            })
        };
        for k in j + 1..equations.len() {
            let delays: Vec<usize> = refs(&equations[k].rule)
                .into_iter()
                .filter_map(|r| match r {
                    Ref::Other(i, d) if i == j => Some(d),
                    _ => None,
                })
                .collect();
            if delays.is_empty() {
                continue;
            }
            // The values of the equation `k` where the rule of `j` is replaced
            let order = equations[k].order();
            let mut values = vec![];
            for n in delays
                .iter()
                .flat_map(|d| exceptions.iter().map(move |o| o + *d as i64))
            {
                if equations[k].given(n, order).is_some() || values.iter().any(|(m, _)| *m == n) {
                    continue;
                }
                let prefix = Sequence {
                    equations: equations[..=k].to_vec().into(),
                };
                values.push((n, prefix.at(set, n)));
            }
            if values.iter().any(|(_, value)| value.is_none()) {
                continue;
            }
            let mut equation = equations[k].rename(&|i, d| (i == j).then(|| at(d)));
            equation.overrides.extend(
                values
                    .into_iter()
                    .map(|(n, value)| (n, value.expect("Checked above"))),
            );
            equation.overrides.sort_by_key(|(n, _)| *n);
            equations[k] = equation;
        }
    }
}

/// A last equation `{$v(n) = u_j(n)$}` without overrides is the sequence `{$u_j$}`.
fn alias<K: SequenceValues>(equations: &mut Vec<Equation<K>>) {
    if let Some(last) = equations.last()
        && last.overrides.is_empty()
        && let Term::Symbol(s) = &last.rule
        && let Some(Ref::Other(j, 0)) = Ref::parse(s.symbol)
    {
        equations.truncate(j + 1);
    }
}

/// Keep the equations the last one depends on.
fn prune<K: SequenceValues>(equations: Vec<Equation<K>>) -> Vec<Equation<K>> {
    let mut used = vec![false; equations.len()];
    if let Some(last) = used.last_mut() {
        *last = true;
    }
    for j in (0..equations.len()).rev() {
        if used[j] {
            for r in refs(&equations[j].rule) {
                if let Ref::Other(i, _) = r {
                    used[i] = true;
                }
            }
        }
    }
    reindex(equations, |j| used[j])
}

/// Merge the equations equal to an earlier one.
fn dedupe<K: SequenceValues>(equations: Vec<Equation<K>>) -> Vec<Equation<K>> {
    let set = equations.first().map(|e| e.rule.get_set());
    let Some(set) = set else { return equations };
    let mut kept: Vec<Equation<K>> = vec![];
    let mut map = vec![];
    for equation in equations {
        let equation = equation.rename(&|j, d| Some(Ref::Other(map[j], d).term(set)));
        if let Some(position) = kept.iter().position(|e| *e == equation) {
            map.push(position);
        } else {
            map.push(kept.len());
            kept.push(equation);
        }
    }
    kept
}

/// Keep the equations `j` with `keep(j)`, renumbering the references.
fn reindex<K: SequenceValues>(
    equations: Vec<Equation<K>>,
    keep: impl Fn(usize) -> bool,
) -> Vec<Equation<K>> {
    if (0..equations.len()).all(&keep) {
        return equations;
    }
    let mut map = vec![0; equations.len()];
    let mut res = vec![];
    for (j, equation) in equations.into_iter().enumerate() {
        if keep(j) {
            map[j] = res.len();
            let set = equation.rule.get_set();
            res.push(equation.rename(&|i, d| Some(Ref::Other(map[i], d).term(set))));
        }
    }
    res
}
