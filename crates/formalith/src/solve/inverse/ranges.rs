//! Ranges of the integer parameters of periodic solutions for which they are real, like `{$k >= 0$}` in
//! `{$x = sqrt(pi/6 + 2 k pi)$}`.
//!
//! The conditions are those of the domains of the functions of the solution: bases of even roots are
//! non-negative, arguments of `ln` positive and those of `asin` and `acos` in `{$[-1, 1]$}`. When they are affine in
//! a parameter `k`, they bound it: a finite range is listed value by value, `{$k >= k_0$}` is written
//! `{$k = k_0 + n$}` and `{$k <= k_1$}` is written `{$k = k_1 - n$}` with a natural parameter `n` (`n`, `n_1`...,
//! see [`is_natural_parameter`]), and an empty range drops the solution. Other conditions leave it unchecked.

use std::{cmp::Ordering, collections::BTreeSet};

use malachite::{Integer, Rational, base::num::arithmetic::traits::Floor};

use crate::{
    context::{Context, Symbol},
    field::real::{
        Real,
        approx::approximate,
        expr::{DIGITS, Expr, constant_sign, depends, subs, unary, value, variable},
    },
    term::{Expand, Normalize, Term},
};

use super::{is_integer_parameter, linear};

/// The most values listed for a parameter with a finite range.
const MAX_LISTED: u32 = 100;

/// Whether `symbol` is named like a natural parameter of a periodic solution, `n` or `n_i`.
pub fn is_natural_parameter(symbol: Symbol) -> bool {
    let name = symbol.name();
    name == "n"
        || name
            .strip_prefix("n_")
            .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
}

/// The solutions `values` with their integer parameters restricted to the values for which they are real, `used`
/// being the symbols of the equation.
pub(super) fn restrict(values: Vec<Expr>, used: &BTreeSet<Symbol>) -> Vec<Expr> {
    values
        .into_iter()
        .flat_map(|solution| restrict_with(solution, vec![], used))
        .collect()
}

/// The values of `c` with its integer parameters restricted to the values for which it is real and every
/// condition `{$u >= 0$}` (`{$u > 0$}` when strict) holds, like `{$c >= 0$}` for `{$sqrt u = c$}`.
pub(super) fn restrict_with(
    c: Expr,
    conditions: Vec<(Expr, bool)>,
    used: &BTreeSet<Symbol>,
) -> Vec<Expr> {
    let parameters = c
        .symbols()
        .into_iter()
        .filter(|s| is_integer_parameter(*s) && !used.contains(s));
    let candidate = Candidate {
        term: c,
        conditions: conditions
            .into_iter()
            .map(|(u, strict)| Condition { u, strict })
            .collect(),
    };
    parameters
        .into_iter()
        .fold(vec![candidate], |res, k| {
            res.into_iter()
                .flat_map(|candidate| restrict_parameter(candidate, k, used))
                .collect()
        })
        .into_iter()
        .map(|candidate| candidate.term)
        .collect()
}

/// A condition `{$u >= 0$}`, or `{$u > 0$}` when strict.
struct Condition {
    u: Expr,
    strict: bool,
}

/// A term with conditions on its parameters other than those for it to be real.
struct Candidate {
    term: Expr,
    conditions: Vec<Condition>,
}

impl Candidate {
    /// The candidate with `value` in place of `k`, expanded so that the bound is merged with the other terms.
    fn subs(&self, k: Symbol, value: &Expr) -> Self {
        Self {
            term: subs(&self.term, k, value).expand(),
            conditions: self
                .conditions
                .iter()
                .map(|condition| Condition {
                    u: subs(&condition.u, k, value).normalize(),
                    strict: condition.strict,
                })
                .collect(),
        }
    }
}

/// The candidates for the integers `k` for which it is real and its conditions hold (see the module
/// documentation).
fn restrict_parameter(candidate: Candidate, k: Symbol, used: &BTreeSet<Symbol>) -> Vec<Candidate> {
    let mut conditions = vec![];
    collect_conditions(&candidate.term, k, &mut conditions);
    let extra = candidate
        .conditions
        .iter()
        .filter(|condition| depends(&condition.u, k));
    let (mut lower, mut upper): (Option<Integer>, Option<Integer>) = (None, None);
    for Condition { u, strict } in conditions.iter().chain(extra) {
        let strict = *strict;
        let other_parameter = u.symbols().into_iter().any(|s| {
            s != k && !used.contains(&s) && (is_integer_parameter(s) || is_natural_parameter(s))
        });
        if other_parameter {
            return vec![candidate];
        }
        let Some((slope, intercept)) = linear(u, k) else {
            return vec![candidate];
        };
        let holds =
            |sign: Ordering| sign == Ordering::Greater || (!strict && sign == Ordering::Equal);
        match constant_sign(&slope) {
            Some(Ordering::Equal) => match constant_sign(&intercept) {
                Some(sign) if holds(sign) => {}
                Some(_) => return vec![],
                None => return vec![candidate],
            },
            // `{$k >= -b/a$}`
            Some(Ordering::Greater) => {
                let Some(bound) = round(&(-intercept / slope).normalize(), strict, true) else {
                    return vec![candidate];
                };
                lower = Some(lower.map_or(bound.clone(), |l| l.max(bound)));
            }
            Some(Ordering::Less) => {
                let Some(bound) = round(&(-intercept / slope).normalize(), strict, false) else {
                    return vec![candidate];
                };
                upper = Some(upper.map_or(bound.clone(), |u| u.min(bound)));
            }
            None => return vec![candidate],
        }
    }
    let int = |n: Integer| value(Rational::from(n));
    // There are infinitely many names, one of them is free
    #[allow(clippy::maybe_infinite_iter)]
    let natural = || {
        let taken = candidate.term.symbols();
        std::iter::once("n".to_owned())
            .chain((1..).map(|i| format!("n_{i}")))
            .map(Symbol::new)
            .find(|s| !used.contains(s) && !taken.contains(s))
            .map(variable)
            .expect("There are infinitely many names")
    };
    match (lower, upper) {
        (Some(l), Some(u)) if l > u => vec![],
        (Some(l), Some(u)) => {
            if &u - &l >= MAX_LISTED {
                return vec![candidate];
            }
            let mut res = vec![];
            let mut i = l;
            while i <= u {
                res.push(candidate.subs(k, &int(i.clone())));
                i += Integer::from(1);
            }
            res
        }
        (Some(l), None) => vec![candidate.subs(k, &(int(l) + natural()))],
        (None, Some(u)) => vec![candidate.subs(k, &(int(u) - natural()))],
        (None, None) => vec![candidate],
    }
}

/// The smallest integer `{$>= "bound"$}` (`>` when strict) when `up`, else the largest `{$<= "bound"$}` (`<`).
/// `None` if the sign of `bound` minus an integer can't be found.
fn round(bound: &Expr, strict: bool, up: bool) -> Option<Integer> {
    let approximation = match bound {
        Term::Value(v) => v.value.clone(),
        _ => approximate(bound, DIGITS)?,
    };
    // The integer `m` closest to the bound, which is compared exactly with it
    let m = (approximation + Rational::from_signeds(1, 2)).floor();
    let one = Integer::from(1);
    Some(
        match (
            constant_sign(&(bound - &value(Rational::from(m.clone()))))?,
            up,
        ) {
            (Ordering::Equal, true) if strict => m + one,
            (Ordering::Equal, false) if strict => m - one,
            (Ordering::Equal, _) | (Ordering::Greater, false) | (Ordering::Less, true) => m,
            (Ordering::Greater, true) => m + one,
            (Ordering::Less, false) => m - one,
        },
    )
}

/// Collect the conditions for `term` to be real on its subterms depending on `k`.
fn collect_conditions(term: &Expr, k: Symbol, conditions: &mut Vec<Condition>) {
    if !depends(term, k) {
        return;
    }
    let mut push = |u: &Expr, strict: bool| {
        if depends(u, k) {
            conditions.push(Condition {
                u: u.clone(),
                strict,
            });
        }
    };
    match term {
        Term::Value(_) | Term::Symbol(_) => {}
        Term::Add(add) => add
            .iter()
            .for_each(|t| collect_conditions(t, k, conditions)),
        Term::Mul(mul) => mul
            .iter()
            .for_each(|t| collect_conditions(t, k, conditions)),
        Term::Pow(pow) => {
            if let Term::Value(e) = &**pow.exponant
                && e.value.denominator_ref() % malachite::Natural::from(2u32) == 0u32
            {
                push(&pow.base, e.value < 0);
            }
            collect_conditions(&pow.base, k, conditions);
            collect_conditions(&pow.exponant, k, conditions);
        }
        Term::Fun(function) => {
            match unary(term) {
                Some((Context::LN, u)) => push(u, true),
                Some((Context::ASIN | Context::ACOS, u)) => {
                    let one = value(Rational::from(1));
                    push(&(&one - u).normalize(), false);
                    push(&(&one + u).normalize(), false);
                }
                _ => {}
            }
            if let Some(args) = function.get_args::<Real>() {
                for t in args {
                    collect_conditions(t, k, conditions);
                }
            }
        }
    }
}
