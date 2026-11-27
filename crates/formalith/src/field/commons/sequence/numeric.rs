//! Sequences of `R^N` evaluated with `f64`, to plot their terms.
//!
//! A [`Sequence`] is compiled once into a [`NumericSequence`]: each rule, initial value and override becomes a
//! [`Numeric`] in the variables `[n, y, params..., refs...]`, like the graphs of real expressions (`y` being unused),
//! the references to the sequences of the system coming last. Its terms are then computed by iterating the system
//! in floats.
//!
//! ```
//! use formalith::{
//!     field::{Set, real::R, sequence::numeric::NumericSequence},
//!     parse, symbol,
//! };
//!
//! let set = R.get_sequence_set(symbol!("n"));
//! let u = parse!("recurrence(u(n) = 2 u(n - 1) + 1, u(0) = 1)", set);
//! let u = NumericSequence::of_term(&u, symbol!("n"), &[]).unwrap();
//! assert_eq!(u.terms(&[], 0, 3), [(0, 1.), (1, 3.), (2, 7.), (3, 15.)]);
//! ```

// Indices and orders are small
#![allow(
    clippy::cast_precision_loss,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_possible_truncation
)]

use std::collections::{BTreeSet, VecDeque};

use super::{MAX_SEQUENCE_STEPS, Ref, Seq, Sequence};
use crate::{
    context::Symbol,
    field::real::{
        Real,
        numeric::{Numeric, free_symbols},
    },
    term::Term,
};

/// An equation of a [`NumericSequence`], see [`Equation`](super::Equation).
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NumericEquation {
    /// The index of the first initial value, for a recurrence.
    pub start: i64,
    /// The order, the number of initial values.
    pub order: usize,
    /// The initial values.
    pub initial: Vec<Numeric>,
    /// The values replacing the rule, by increasing index.
    pub overrides: Vec<(i64, Numeric)>,
    /// The general term, in the variables `[n, y, params..., refs...]`.
    pub rule: Numeric,
    /// The reference standing for each variable after the parameters: the equation and the shift `d` of its
    /// value at `{$n - d$}`.
    pub refs: Vec<(usize, usize)>,
}

/// A sequence of `R^N` evaluated with `f64`, see the [module documentation](self).
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NumericSequence {
    /// The equations of the system, the last one being the sequence.
    pub equations: Vec<NumericEquation>,
}

impl NumericSequence {
    /// The symbols the sequence depends on: the index and its parameters.
    #[must_use]
    pub fn symbols(sequence: &Sequence<Real>) -> BTreeSet<Symbol> {
        sequence
            .equations()
            .iter()
            .flat_map(|equation| {
                equation
                    .initial
                    .iter()
                    .chain(equation.overrides.iter().map(|(_, value)| value))
                    .chain([&equation.rule])
            })
            .flat_map(free_symbols)
            .filter(|symbol| Ref::parse(*symbol).is_none())
            .collect()
    }

    /// Compile `sequence`, indexed by `index`, with the parameters `params`.
    #[must_use]
    pub fn compile(sequence: &Sequence<Real>, index: Symbol, params: &[Symbol]) -> Self {
        // `y` is never a symbol of the sequence
        let unused = Symbol::new("@y");
        let vars: Vec<Symbol> = [index, unused]
            .into_iter()
            .chain(params.iter().copied())
            .collect();
        let equations = sequence
            .equations()
            .iter()
            .enumerate()
            .map(|(j, equation)| {
                let refs: Vec<Ref> = equation
                    .rule
                    .symbols()
                    .into_iter()
                    .filter_map(Ref::parse)
                    .collect();
                let rule_vars: Vec<Symbol> = vars
                    .iter()
                    .copied()
                    .chain(refs.iter().map(|r| r.symbol()))
                    .collect();
                let compile = |term: &Term<Real>| Numeric::compile(term, &vars);
                NumericEquation {
                    start: equation.start,
                    order: equation.order(),
                    initial: equation.initial.iter().map(compile).collect(),
                    overrides: equation
                        .overrides
                        .iter()
                        .map(|(m, value)| (*m, compile(value)))
                        .collect(),
                    rule: Numeric::compile(&equation.rule, &rule_vars),
                    refs: refs
                        .iter()
                        .map(|r| match *r {
                            Ref::Own(d) => (j, d),
                            Ref::Other(i, d) => (i, d),
                        })
                        .collect(),
                }
            })
            .collect();
        Self { equations }
    }

    /// Compile a sequence of `R^N` given as a term, `None` if it isn't a single value.
    #[must_use]
    pub fn of_term(term: &Term<Seq<Real>>, index: Symbol, params: &[Symbol]) -> Option<Self> {
        match term {
            Term::Value(value) => Some(Self::compile(&value.value, index, params)),
            _ => None,
        }
    }

    /// The name of the first part which can't be evaluated numerically, like `integrate`.
    #[must_use]
    pub fn unsupported(&self) -> Option<&str> {
        self.equations.iter().find_map(|equation| {
            equation
                .initial
                .iter()
                .chain(equation.overrides.iter().map(|(_, value)| value))
                .chain([&equation.rule])
                .find_map(Numeric::unsupported)
        })
    }

    /// The finite terms of indices from `from` to `to`, with the values `params` of the parameters. Nothing is
    /// computed if it would take more than [`MAX_SEQUENCE_STEPS`] terms.
    #[must_use]
    pub fn terms(&self, params: &[f64], from: i64, to: i64) -> Vec<(i64, f64)> {
        let delay = self
            .equations
            .iter()
            .flat_map(|equation| equation.refs.iter().map(|(_, d)| *d))
            .max()
            .unwrap_or(0);
        let history = (delay * self.equations.len()) as i64;
        let low = self
            .equations
            .iter()
            .filter(|equation| equation.order > 0)
            .map(|equation| equation.start)
            .fold(from.saturating_sub(history), i64::min);
        if from > to || to.saturating_sub(low) > MAX_SEQUENCE_STEPS {
            return vec![];
        }
        let mut vars: Vec<f64> = [f64::NAN, f64::NAN]
            .into_iter()
            .chain(params.iter().copied())
            .collect();
        let base = vars.len();
        // The last values of each equation, from `{$n - "delay"$}` to `n`
        let mut windows: Vec<VecDeque<f64>> = vec![VecDeque::new(); self.equations.len()];
        let mut terms = vec![];
        for n in low..=to {
            vars[0] = n as f64;
            for (j, equation) in self.equations.iter().enumerate() {
                let given = if equation.order > 0
                    && (equation.start..equation.start + equation.order as i64).contains(&n)
                {
                    equation.initial.get((n - equation.start) as usize)
                } else {
                    equation
                        .overrides
                        .iter()
                        .find(|(m, _)| *m == n)
                        .map(|(_, value)| value)
                };
                let value = match given {
                    Some(value) => value.eval(&vars[..base]),
                    None if equation.order > 0 && n < equation.start => f64::NAN,
                    None => {
                        vars.truncate(base);
                        vars.extend(equation.refs.iter().map(|&(i, d)| {
                            let window = &windows[i];
                            // The value of an earlier equation at `n` is already in its window
                            let back = if i == j { d } else { d + 1 };
                            window
                                .len()
                                .checked_sub(back)
                                .map_or(f64::NAN, |position| window[position])
                        }));
                        equation.rule.eval(&vars)
                    }
                };
                let window = &mut windows[j];
                window.push_back(value);
                if window.len() > delay + 1 {
                    window.pop_front();
                }
            }
            if n >= from {
                let value = windows
                    .last()
                    .and_then(VecDeque::back)
                    .copied()
                    .unwrap_or(f64::NAN);
                if value.is_finite() {
                    terms.push((n, value));
                }
            }
        }
        terms
    }
}
