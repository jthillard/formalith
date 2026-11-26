//! Case splits on the signs of parameters.
//!
//! A calculus builtin (`lim`, `series`, `integrate`, `sum`, `product`) staying unevaluated because the sign of a
//! parameter is unknown is evaluated again for each of its signs, the results being joined in a `piecewise`:
//! `{$integrate(sqrt(r/x - 1), x, 0, r) = (pi r)/2$}` without assumption on `r`, every branch agreeing. The sign
//! engine records the symbols whose sign it couldn't decide during the evaluation ([`record`]), the first of them
//! (by name) among the parameters of the call is split on, at most [`MAX_SPLIT_SYMBOLS`] of them in nested splits.
//! Negative and positive signs are assumed, zero is substituted. A branch still unevaluated keeps the call as its
//! value.

use std::{
    cell::{Cell, RefCell},
    collections::BTreeSet,
};

use super::expr::{Expr, subs, zero};
use crate::{
    context::{
        Context, Symbol,
        assumptions::{Assumption, Assumptions, SignSet},
    },
    term::{Expand, Fun, Term, flags::Flags, relation::Relation},
};

/// Number of parameters a call is split on at most, in nested splits.
pub const MAX_SPLIT_SYMBOLS: usize = 2;

thread_local! {
    /// The symbols whose sign the sign engine couldn't decide, while recording.
    static RECORDING: RefCell<Option<BTreeSet<Symbol>>> = const { RefCell::new(None) };
    /// Whether a split evaluation is running, builtins evaluated inside it don't split.
    static SPLITTING: Cell<bool> = const { Cell::new(false) };
}

/// Record that the sign of `symbol` couldn't be decided, when recording.
pub fn record(symbol: Symbol) {
    RECORDING.with_borrow_mut(|recording| {
        if let Some(symbols) = recording {
            symbols.insert(symbol);
        }
    });
}

/// Stops splitting, then recording, when dropped (also on panics).
struct Guard;

impl Drop for Guard {
    fn drop(&mut self) {
        RECORDING.with_borrow_mut(|current| *current = None);
        SPLITTING.set(false);
    }
}

/// Evaluate the call `ident(args)` with `eval` (`None` when it stays unevaluated), splitting on the signs of its
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
    split(ident, args, bound, eval, MAX_SPLIT_SYMBOLS)
}

/// `eval(args)` and the symbols whose sign was undecided during it. Evaluations of [`split`] are sequential, so
/// recordings don't nest.
fn recorded(
    eval: &dyn Fn(&[Expr]) -> Option<Expr>,
    args: &[Expr],
) -> (Option<Expr>, BTreeSet<Symbol>) {
    RECORDING.set(Some(BTreeSet::new()));
    let res = eval(args);
    let symbols = RECORDING.take().unwrap_or_default();
    (res, symbols)
}

/// Add to `symbols` the variables bound by the calculus builtins and held sums in `term`, like `k` in
/// `{$sum_(k = 0)^oo x^k$}`.
fn bound_symbols(term: &Expr, symbols: &mut BTreeSet<Symbol>) {
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

/// See [`evaluate`].
fn split(
    ident: Symbol,
    args: &[Expr],
    bound: Symbol,
    eval: &dyn Fn(&[Expr]) -> Option<Expr>,
    budget: usize,
) -> Option<Expr> {
    let (res, undecided) = recorded(eval, args);
    if res.is_some() || budget == 0 {
        return res;
    }
    let (mut parameters, mut bound_inside) = (BTreeSet::new(), BTreeSet::new());
    for arg in args {
        arg.collect_symbols(&mut parameters);
        bound_symbols(arg, &mut bound_inside);
    }
    let mut candidates: Vec<Symbol> = undecided
        .intersection(&parameters)
        .copied()
        .filter(|&s| {
            s != bound
                && !bound_inside.contains(&s)
                && !Context::is_builtin_constant(s)
                && !s.name().starts_with('@')
        })
        .collect();
    candidates.sort_by_key(|s| s.name());
    let s = *candidates.first()?;
    let signs = Assumptions::current().get(s).sign;

    let mut any = false;
    // The value of each branch, and whether it was evaluated
    let mut branch = |sign: SignSet| -> Option<(Expr, bool)> {
        if !signs.contains(sign.strict()?) {
            return None;
        }
        let res = if sign == SignSet::ZERO {
            let args: Vec<Expr> = args.iter().map(|arg| subs(arg, s, &zero())).collect();
            split(ident, &args, bound, eval, budget - 1).ok_or(args)
        } else {
            let mut assumptions = Assumptions::current();
            assumptions.assume(s, Assumption::sign(sign)).ok()?;
            let _assumed = assumptions.enter();
            split(ident, args, bound, eval, budget - 1).ok_or_else(|| args.to_vec())
        };
        any |= res.is_ok();
        let evaluated = res.is_ok();
        // Its arguments are normalized, normalizing the held call would evaluate it again
        Some((
            res.unwrap_or_else(|args| normalized_call(ident, args)),
            evaluated,
        ))
    };
    let negative = branch(SignSet::NEGATIVE);
    let zero_value = branch(SignSet::ZERO).map(|(value, _)| value);
    let positive = branch(SignSet::POSITIVE);
    if !any {
        return None;
    }
    Some(join(s, negative, zero_value, positive))
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

/// The condition `s rel 0`.
fn condition(s: Symbol, relation: Relation) -> Expr {
    normalized_call(relation.symbol(), vec![super::expr::variable(s), zero()])
}

/// The `piecewise` of the values on the negative, zero and positive sides of `s` (with whether they were
/// evaluated), merged when they agree. The zero value isn't merged into a held call, which substituting `s`
/// would evaluate.
fn join(
    s: Symbol,
    negative: Option<(Expr, bool)>,
    zero_value: Option<Expr>,
    positive: Option<(Expr, bool)>,
) -> Expr {
    let at_zero = |value: &Expr| subs(value, s, &zero());
    let mergeable = |side: &Option<(Expr, bool)>, z: &Expr| {
        side.as_ref()
            .is_some_and(|(value, evaluated)| *evaluated && equal(&at_zero(value), z))
    };
    // The zero value merged into a side
    let zero_side = match &zero_value {
        Some(z) if mergeable(&positive, z) => Some(Relation::GreaterEqual),
        Some(z) if mergeable(&negative, z) => Some(Relation::LessEqual),
        _ => None,
    };
    let zero_value = zero_value.filter(|_| zero_side.is_none());
    let (negative, positive) = (negative.map(|(v, _)| v), positive.map(|(v, _)| v));
    let mut args = vec![];
    match (negative, zero_value, positive) {
        (Some(n), None, Some(p)) if equal(&n, &p) => return n,
        (Some(n), None, Some(p)) => {
            let relation = if zero_side == Some(Relation::LessEqual) {
                Relation::LessEqual
            } else {
                Relation::Less
            };
            args.extend([condition(s, relation), n, p]);
        }
        (Some(n), Some(z), Some(p)) if equal(&n, &p) => {
            args.extend([condition(s, Relation::Equal), z, n]);
        }
        (Some(n), Some(z), Some(p)) => {
            args.extend([
                condition(s, Relation::Less),
                n,
                condition(s, Relation::Equal),
                z,
                p,
            ]);
        }
        // A sign excluded by the assumptions
        (Some(v), None, None) | (None, Some(v), None) | (None, None, Some(v)) => return v,
        (None, Some(z), Some(p)) => args.extend([condition(s, Relation::Equal), z, p]),
        (Some(n), Some(z), None) => args.extend([condition(s, Relation::Equal), z, n]),
        (None, None, None) => unreachable!("a branch succeeded"),
    }
    super::R
        .eval_piecewise(&args)
        .unwrap_or_else(|| normalized_call(Context::PIECEWISE, args))
}
