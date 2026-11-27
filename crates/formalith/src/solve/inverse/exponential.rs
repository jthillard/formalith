//! Sums of exponentials of different bases `{$c_0 + sum c_i e^(lambda_i u) = 0$}`, like `{$2^x + 3^x = 5$}`, with
//! constant coefficients and rates and a common `u`.
//!
//! By Descartes' rule of signs for exponential sums, the number of real roots `u` is at most the number `N` of sign
//! changes of the coefficients sorted by rate, so there is none for `{$N = 0$}`. The roots are isolated numerically
//! (between the critical points of `{$e^(-lambda_0 u) f$}`, found recursively since its derivative has one term
//! less), then rational numbers with small denominators close to them are checked exactly. The equation is solved
//! when `N` exact roots are found, these being then every root.

use std::cmp::Ordering;

use malachite::{Integer, Rational};

use crate::{
    context::{Context, Symbol},
    field::real::{
        expr::{Expr, constant_sign, depends, fun, int, map_tree, subs, unary, value, variable},
        numeric::Numeric,
    },
    term::{Expand, Normalize, Term},
};

use super::{Inverter, Kernel, SolveError, plain};

/// Largest denominator of the rational roots tried.
const MAX_DENOMINATOR: i64 = 12;

/// A term `{$c e^(lambda u)$}`, with floating-point approximations.
struct Exponential {
    rate: f64,
    coefficient: f64,
}

impl Inverter {
    /// The values of the unknown such that `expression = 0`, if it is a sum of exponentials of a common `u` with
    /// constant coefficients and rates (see the module documentation). `None` if it doesn't have this form.
    pub(super) fn exponential_sum(
        &self,
        expression: &Expr,
        kernels: &[Kernel],
        depth: usize,
    ) -> Option<Result<Vec<Expr>, SolveError>> {
        let x = self.x;
        // The common `u`, and the rate of each kernel
        let mut angle: Option<&Expr> = None;
        let mut rates = vec![];
        for kernel in kernels {
            let (u, rate) = match (unary(&kernel.base), &kernel.base) {
                (Some((Context::EXP, u)), _) => (u, value(kernel.exponent.clone())),
                (_, Term::Pow(pow)) if !depends(&pow.base, x) && depends(&pow.exponant, x) => (
                    &**pow.exponant,
                    value(kernel.exponent.clone()) * fun(Context::LN, (*pow.base).clone()),
                ),
                _ => return None,
            };
            if angle.is_some_and(|angle| angle != u) {
                return None;
            }
            angle = Some(u);
            rates.push(rate.normalize());
        }
        let u = angle?.clone();
        // `{$c_0 + sum c_i s_i$}` with a symbol `{$s_i$}` per kernel
        let symbols: Vec<Symbol> = (0..kernels.len())
            .map(|i| Symbol::new(format!("@e{depth}_{i}")))
            .collect();
        let replaced = map_tree(expression, &|term| {
            kernels
                .iter()
                .zip(&symbols)
                .find(|(kernel, _)| kernel.term == *term)
                .map(|(kernel, s)| &kernel.factor * &variable(*s))
        })
        .expand();
        let zero = int(0);
        let constant = symbols
            .iter()
            .fold(replaced.clone(), |res, s| subs(&res, *s, &zero));
        let mut terms = vec![(zero, constant)];
        for (s, rate) in symbols.iter().zip(rates) {
            terms.push((rate, replaced.derivative(*s).normalize()));
        }
        let numeric = |term: &Expr| {
            let n = Numeric::compile(term, &[]);
            if n.unsupported().is_some() {
                return None;
            }
            Some(n.eval(&[])).filter(|v| v.is_finite())
        };
        // Exact signs and floating-point values, the rates being sorted exactly
        let mut exponentials: Vec<(Exponential, Ordering, &Expr)> = vec![];
        for (rate, coefficient) in &terms {
            if depends(coefficient, x) || symbols.iter().any(|s| depends(coefficient, *s)) {
                return None;
            }
            let sign = constant_sign(coefficient)?;
            constant_sign(rate)?;
            if sign == Ordering::Equal {
                continue;
            }
            let exponential = Exponential {
                rate: numeric(rate)?,
                coefficient: numeric(coefficient)?,
            };
            // Insertion by the exact order of the rates, close floats being compared exactly
            let mut index = exponentials.len();
            for (i, (other, _, other_rate)) in exponentials.iter().enumerate() {
                let (p, q) = (exponential.rate, other.rate);
                let order = if (p - q).abs() > 1e-9 * p.abs().max(q.abs()).max(1.0) {
                    p.partial_cmp(&q)?
                } else {
                    constant_sign(&(rate - *other_rate).normalize())?
                };
                match order {
                    // Equal rates should have been merged
                    Ordering::Equal => return None,
                    Ordering::Less => {
                        index = index.min(i);
                    }
                    Ordering::Greater => {}
                }
            }
            exponentials.insert(index, (exponential, sign, rate));
        }
        let changes = exponentials.windows(2).filter(|w| w[0].1 != w[1].1).count();
        if changes == 0 {
            return Some(Ok(vec![]));
        }
        let terms: Vec<Exponential> = exponentials.into_iter().map(|(t, _, _)| t).collect();
        // Rational roots close to the approximate ones, checked exactly
        let mut exact: Vec<Rational> = vec![];
        for root in real_roots(&terms) {
            for q in 1..=MAX_DENOMINATOR {
                #[allow(clippy::cast_precision_loss, clippy::cast_possible_truncation)]
                let p = (root * q as f64).round();
                #[allow(clippy::cast_precision_loss)]
                if (p / q as f64 - root).abs() > 1e-6 || p.abs() > 1e15 {
                    continue;
                }
                #[allow(clippy::cast_possible_truncation)]
                let r = Rational::from(Integer::from(p as i64)) / Rational::from(q);
                if exact.contains(&r) {
                    break;
                }
                if vanishes_at(&replaced, kernels, &symbols, &r) {
                    exact.push(r);
                    break;
                }
            }
        }
        if exact.len() != changes {
            return Some(Err(SolveError::Unsolvable(plain(expression))));
        }
        let mut res = vec![];
        for r in exact {
            match self.solve(&(&u - &value(r)), depth + 1) {
                Ok(values) => res.extend(values),
                Err(error) => return Some(Err(error)),
            }
        }
        Some(Ok(res))
    }
}

/// Whether `{$c_0 + sum c_i s_i$}` vanishes exactly for `{$u = r$}`, `{$s_i$}` standing for the kernels.
fn vanishes_at(replaced: &Expr, kernels: &[Kernel], symbols: &[Symbol], r: &Rational) -> bool {
    let at = kernels
        .iter()
        .zip(symbols)
        .fold(replaced.clone(), |res, (kernel, s)| {
            let exponent = value(&kernel.exponent * r);
            let power = match (unary(&kernel.base), &kernel.base) {
                (Some((Context::EXP, _)), _) => fun(Context::EXP, exponent),
                (_, Term::Pow(pow)) => pow.base.pow(&exponent),
                _ => return res,
            };
            subs(&res, *s, &power)
        });
    let at = at.normalize();
    at.expand().is_zero() || constant_sign(&at) == Some(Ordering::Equal)
}

/// `{$sum c_i e^(lambda_i u)$}`.
fn evaluate(terms: &[Exponential], u: f64) -> f64 {
    terms
        .iter()
        .map(|t| t.coefficient * (t.rate * u).exp())
        .sum()
}

/// The approximate real roots of `{$sum c_i e^(lambda_i u)$}`, with increasing rates: `{$e^(-lambda_0 u)$}` times
/// it is monotonic between the roots of its derivative, which has one term less.
fn real_roots(terms: &[Exponential]) -> Vec<f64> {
    if terms.len() < 2 {
        return vec![];
    }
    let shifted: Vec<Exponential> = terms
        .iter()
        .map(|t| Exponential {
            rate: t.rate - terms[0].rate,
            coefficient: t.coefficient,
        })
        .collect();
    let derivative: Vec<Exponential> = shifted[1..]
        .iter()
        .map(|t| Exponential {
            rate: t.rate,
            coefficient: t.coefficient * t.rate,
        })
        .collect();
    let critical = real_roots(&derivative);
    let f = |u: f64| evaluate(&shifted, u);
    let sign = |v: f64| v.partial_cmp(&0.0);
    let mut res = vec![];
    // The ends of the monotonic pieces, infinite ends being pushed until the sign of the limit
    let first = critical.first().copied().unwrap_or(0.0);
    let last = critical.last().copied().unwrap_or(0.0);
    let towards = |start: f64, direction: f64, limit: f64| {
        let mut step = 1.0;
        for _ in 0..64 {
            let u = start + direction * step;
            if sign(f(u)) == sign(limit) {
                return Some(u);
            }
            step *= 2.0;
        }
        None
    };
    let mut ends = vec![];
    if let Some(u) = towards(first, -1.0, shifted[0].coefficient) {
        ends.push(u);
    }
    ends.extend(&critical);
    if let Some(u) = towards(
        last,
        1.0,
        shifted.last().expect("There are terms").coefficient,
    ) {
        ends.push(u);
    }
    for w in ends.windows(2) {
        let (mut a, mut b) = (w[0], w[1]);
        let (fa, fb) = (f(a), f(b));
        if fa == 0.0 {
            res.push(a);
            continue;
        }
        if sign(fa) == sign(fb) || fb.is_nan() || fa.is_nan() {
            continue;
        }
        for _ in 0..200 {
            let m = f64::midpoint(a, b);
            if m <= a || m >= b {
                break;
            }
            if sign(f(m)) == sign(fa) {
                a = m;
            } else {
                b = m;
            }
        }
        res.push(f64::midpoint(a, b));
    }
    if let Some(&last) = ends.last()
        && f(last) == 0.0
    {
        res.push(last);
    }
    res
}
