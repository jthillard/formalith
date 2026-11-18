//! Bounds of constant terms containing angles, by interval arithmetic.
//!
//! When `{$g -> plus.minus oo$}`, `{$sin g$}` and `{$cos g$}` oscillate without a limit. They are replaced by
//! `{$sin theta$}` and `{$cos theta$}` for an angle `{$theta$}`, a symbol `@t<n>` treated as a constant by the
//! Gruntz algorithm, whose sine and cosine lie in `{$[-1, 1]$}`.

use std::cmp::Ordering;

use malachite::{
    Rational,
    base::num::{
        arithmetic::traits::Sign,
        basic::traits::{NegativeOne, One, Zero},
    },
};

use crate::{
    context::{Context, Symbol},
    term::Term,
};

use super::{Expr, fun, only_symbols, rational_bound, unary, value};

/// Whether `symbol` is an angle introduced for an oscillating `sin` or `cos`.
pub(super) fn is_angle(symbol: Symbol) -> bool {
    Context::get_symbol_data(&symbol).name.starts_with("@t")
}

/// Whether `term` contains an angle.
pub(super) fn has_angle(term: &Expr) -> bool {
    term.symbols().into_iter().any(is_angle)
}

/// The angles of `term`.
pub(super) fn angles(term: &Expr) -> Vec<Symbol> {
    term.symbols()
        .into_iter()
        .filter(|s| is_angle(*s))
        .collect()
}

/// Bounds `{$[l, h]$}` of a constant term whose only symbols are angles and builtin constants, or `None` if it
/// isn't bounded or has other symbols.
pub(super) fn bounds(term: &Expr) -> Option<(Rational, Rational)> {
    if !has_angle(term) {
        if !only_symbols(term, &[]) {
            return None;
        }
        return Some((
            rational_bound(term, false).ok()?,
            rational_bound(term, true).ok()?,
        ));
    }
    match term {
        Term::Value(_) | Term::Symbol(_) => None,
        Term::Add(add) => {
            add.iter()
                .try_fold((Rational::ZERO, Rational::ZERO), |(lo, hi), term| {
                    let (l, h) = bounds(term)?;
                    Some((lo + l, hi + h))
                })
        }
        Term::Mul(mul) => {
            let c = mul.coefficient.clone();
            mul.iter().try_fold((c.clone(), c), |res, factor| {
                Some(product(&res, &bounds(factor)?))
            })
        }
        Term::Pow(pow) => {
            if has_angle(&pow.exponant) {
                return None;
            }
            let (lo, hi) = bounds(&pow.base)?;
            if let Some(n) = pow.exponant.to_i64() {
                let (lo, hi) = if n < 0 {
                    // `{$1/[l, h] = [1/h, 1/l]$}` when 0 isn't in the interval
                    if lo > Rational::ZERO || hi < Rational::ZERO {
                        (Rational::ONE / hi, Rational::ONE / lo)
                    } else {
                        return None;
                    }
                } else {
                    (lo, hi)
                };
                Some(power(&lo, &hi, n.unsigned_abs()))
            } else {
                let positive = pow.exponant.is_strictly_positive();
                if lo < Rational::ZERO || (!positive && lo == Rational::ZERO) {
                    return None;
                }
                // Monotonic, increasing for a positive exponent
                let at = |x: &Rational, above| {
                    rational_bound(&value(x.clone()).pow(&pow.exponant), above).ok()
                };
                Some(if positive {
                    (at(&lo, false)?, at(&hi, true)?)
                } else {
                    (at(&hi, false)?, at(&lo, true)?)
                })
            }
        }
        Term::Fun(_) => {
            let (ident, arg) = unary(term)?;
            match ident {
                Context::SIN | Context::COS => Some((Rational::NEGATIVE_ONE, Rational::ONE)),
                Context::EXP | Context::LN => {
                    let (lo, hi) = bounds(arg)?;
                    if ident == Context::LN && lo <= Rational::ZERO {
                        return None;
                    }
                    let at = |x: Rational, above| rational_bound(&fun(ident, value(x)), above).ok();
                    Some((at(lo, false)?, at(hi, true)?))
                }
                Context::ABS => {
                    let (lo, hi) = bounds(arg)?;
                    Some(if lo >= Rational::ZERO {
                        (lo, hi)
                    } else if hi <= Rational::ZERO {
                        (-hi, -lo)
                    } else {
                        (Rational::ZERO, if -&lo > hi { -lo } else { hi })
                    })
                }
                _ => None,
            }
        }
    }
}

/// The sign of a constant term containing angles, from its bounds.
pub(super) fn bounds_sign(term: &Expr) -> Option<Ordering> {
    let (lo, hi) = bounds(term)?;
    if lo > Rational::ZERO {
        Some(Ordering::Greater)
    } else if hi < Rational::ZERO {
        Some(Ordering::Less)
    } else {
        None
    }
}

/// The product of two intervals.
fn product((a, b): &(Rational, Rational), (c, d): &(Rational, Rational)) -> (Rational, Rational) {
    let candidates = [a * c, a * d, b * c, b * d];
    let mut lo = candidates[0].clone();
    let mut hi = candidates[0].clone();
    for candidate in candidates {
        if candidate < lo {
            lo = candidate.clone();
        }
        if candidate > hi {
            hi = candidate;
        }
    }
    (lo, hi)
}

/// `{$[l, h]^n$}`.
fn power(lo: &Rational, hi: &Rational, n: u64) -> (Rational, Rational) {
    let pow = |x: &Rational| (0..n).fold(Rational::ONE, |res, _| res * x);
    let (pl, ph) = (pow(lo), pow(hi));
    if n % 2 == 1 || lo.sign() != Ordering::Less {
        (pl, ph)
    } else if hi.sign() != Ordering::Greater {
        (ph, pl)
    } else {
        (Rational::ZERO, if pl > ph { pl } else { ph })
    }
}
