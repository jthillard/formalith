//! Linear relations with rational coefficients, like `{$a - 2 b + 1 > 0$}`, decided by Fourier-Motzkin elimination.
//!
//! Only infeasibility is ever concluded: when the elimination grows too much, the system is taken as feasible, so
//! implications drawn from it stay sound.

use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
};

use malachite::{
    Natural, Rational,
    base::num::{
        arithmetic::traits::{Gcd, Lcm, Sign},
        basic::traits::{One, Zero},
    },
};

use super::SignSet;
use crate::context::Symbol;

/// Constraints above which the elimination gives up, taking the system as feasible.
const MAX_CONSTRAINTS: usize = 400;

/// A variable of a linear form: a symbol, or another term standing for itself, numbered by its user.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Var {
    /// A symbol.
    Symbol(Symbol),
    /// Another term, like `{$e^x$}` in `{$a + e^x$}`.
    Atom(usize),
}

/// `{$sum c_i x_i + c$}`, with rational coefficients `c_i` (none of them zero) and constant `c`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LinearForm {
    /// The non-zero coefficients of the variables.
    pub coefficients: BTreeMap<Var, Rational>,
    /// The constant term.
    pub constant: Rational,
}

impl Default for LinearForm {
    fn default() -> Self {
        Self::constant(Rational::ZERO)
    }
}

impl LinearForm {
    /// The constant `c`.
    #[must_use]
    pub const fn constant(c: Rational) -> Self {
        Self {
            coefficients: BTreeMap::new(),
            constant: c,
        }
    }

    /// The variable `x`.
    #[must_use]
    pub fn variable(x: Var) -> Self {
        let mut res = Self::default();
        res.add_term(x, Rational::ONE);
        res
    }

    /// Add `c x`.
    pub fn add_term(&mut self, x: Var, c: Rational) {
        let coefficient = self.coefficients.entry(x).or_insert(Rational::ZERO);
        *coefficient += c;
        if *coefficient == 0 {
            self.coefficients.remove(&x);
        }
    }

    /// `self + other`.
    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        let mut res = self.clone();
        for (x, c) in &other.coefficients {
            res.add_term(*x, c.clone());
        }
        res.constant += &other.constant;
        res
    }

    /// `c self`.
    #[must_use]
    pub fn scale(&self, c: &Rational) -> Self {
        if *c == 0 {
            return Self::default();
        }
        Self {
            coefficients: self
                .coefficients
                .iter()
                .map(|(x, coefficient)| (*x, coefficient * c))
                .collect(),
            constant: &self.constant * c,
        }
    }

    /// `-self`.
    #[must_use]
    pub fn neg(&self) -> Self {
        self.scale(&-Rational::ONE)
    }

    /// Whether the form has no variable.
    #[must_use]
    pub const fn is_constant(&self) -> bool {
        self.coefficients.is_empty()
    }

    /// The coefficient of `x`, 0 when it doesn't appear.
    #[must_use]
    pub fn coefficient(&self, x: Var) -> Rational {
        self.coefficients.get(&x).cloned().unwrap_or(Rational::ZERO)
    }

    /// The symbols of the form.
    pub fn symbols(&self) -> impl Iterator<Item = Symbol> + '_ {
        self.coefficients.keys().filter_map(|x| match x {
            Var::Symbol(s) => Some(*s),
            Var::Atom(_) => None,
        })
    }

    /// The form multiplied by a positive rational so that its coefficients and constant are coprime integers.
    #[must_use]
    pub fn primitive(&self) -> Self {
        let values = || self.coefficients.values().chain([&self.constant]);
        let denominators = values().fold(Natural::ONE, |res, c| res.lcm(c.denominator_ref()));
        let numerators = values().fold(Natural::ZERO, |res, c| res.gcd(c.numerator_ref()));
        if numerators == 0 {
            return self.clone();
        }
        self.scale(&Rational::from_naturals(denominators, numerators))
    }
}

/// `{$f > 0$}` (`strict`) or `{$f >= 0$}`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constraint {
    /// The form `f`.
    pub form: LinearForm,
    /// Whether the inequality is strict.
    pub strict: bool,
}

impl Constraint {
    /// `{$f > 0$}` (`strict`) or `{$f >= 0$}`.
    #[must_use]
    pub const fn new(form: LinearForm, strict: bool) -> Self {
        Self { form, strict }
    }
}

/// Whether the constraints and the disequalities `{$d != 0$}` have a common real solution.
///
/// A convex set meets the complement of finitely many hyperplanes unless it lies in one of them, so each
/// disequality is checked alone.
#[must_use]
pub fn feasible(constraints: &[Constraint], disequalities: &[LinearForm]) -> bool {
    convex_feasible(constraints.to_vec())
        && disequalities.iter().all(|d| {
            [d.clone(), d.neg()].into_iter().any(|side| {
                let mut constraints = constraints.to_vec();
                constraints.push(Constraint::new(side, true));
                convex_feasible(constraints)
            })
        })
}

/// The possible signs of `form` under the constraints and disequalities, see [`feasible`].
#[must_use]
pub fn signs(
    form: &LinearForm,
    constraints: &[Constraint],
    disequalities: &[LinearForm],
) -> SignSet {
    let with = |extra: &[Constraint]| {
        let mut all = constraints.to_vec();
        all.extend_from_slice(extra);
        feasible(&all, disequalities)
    };
    let mut res = SignSet::EMPTY;
    if with(&[Constraint::new(form.neg(), true)]) {
        res = res.union(SignSet::NEGATIVE);
    }
    if with(&[
        Constraint::new(form.clone(), false),
        Constraint::new(form.neg(), false),
    ]) {
        res = res.union(SignSet::ZERO);
    }
    if with(&[Constraint::new(form.clone(), true)]) {
        res = res.union(SignSet::POSITIVE);
    }
    res
}

/// Whether the constraints have a common real solution, by Fourier-Motzkin elimination.
fn convex_feasible(mut constraints: Vec<Constraint>) -> bool {
    loop {
        // Check the constant constraints, and keep the strictest of identical ones
        let mut kept: BTreeMap<LinearForm, bool> = BTreeMap::new();
        for constraint in constraints {
            if constraint.form.is_constant() {
                match constraint.form.constant.sign() {
                    Ordering::Less => return false,
                    Ordering::Equal if constraint.strict => return false,
                    _ => {}
                }
            } else {
                *kept.entry(constraint.form.primitive()).or_insert(false) |= constraint.strict;
            }
        }
        if kept.is_empty() || kept.len() > MAX_CONSTRAINTS {
            return true;
        }
        let variables: BTreeSet<Var> = kept
            .keys()
            .flat_map(|form| form.coefficients.keys().copied())
            .collect();
        // Eliminate the variable giving the fewest new constraints
        let count = |x: &Var, sign: Ordering| {
            kept.keys()
                .filter(|form| form.coefficients.get(x).is_some_and(|c| c.sign() == sign))
                .count()
        };
        let Some(x) = variables
            .into_iter()
            .min_by_key(|x| count(x, Ordering::Greater) * count(x, Ordering::Less))
        else {
            return true;
        };
        let (mut lower, mut upper, mut rest) = (vec![], vec![], vec![]);
        for (form, strict) in kept {
            match form.coefficient(x).sign() {
                Ordering::Greater => lower.push(Constraint::new(form, strict)),
                Ordering::Less => upper.push(Constraint::new(form, strict)),
                Ordering::Equal => rest.push(Constraint::new(form, strict)),
            }
        }
        for l in &lower {
            for u in &upper {
                // Both multipliers are positive, and the coefficients of `x` cancel
                let form = l
                    .form
                    .scale(&-u.form.coefficient(x))
                    .add(&u.form.scale(&l.form.coefficient(x)));
                rest.push(Constraint::new(form, l.strict || u.strict));
            }
        }
        constraints = rest;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str) -> Var {
        Var::Symbol(Symbol::new(name))
    }

    /// `{$sum c_i x_i + c$}` from `(name, c_i)` pairs.
    fn form(terms: &[(&str, i64)], c: i64) -> LinearForm {
        let mut res = LinearForm::constant(Rational::from(c));
        for (name, coefficient) in terms {
            res.add_term(var(name), Rational::from(*coefficient));
        }
        res
    }

    #[test]
    fn strictness() {
        // `a >= 1`, `a <= 1`
        let closed = [
            Constraint::new(form(&[("a", 1)], -1), false),
            Constraint::new(form(&[("a", -1)], 1), false),
        ];
        assert!(feasible(&closed, &[]));
        assert!(!feasible(&closed, &[form(&[("a", 1)], -1)]));
        let open = [
            Constraint::new(form(&[("a", 1)], -1), true),
            Constraint::new(form(&[("a", -1)], 1), false),
        ];
        assert!(!feasible(&open, &[]));
    }

    #[test]
    fn chains() {
        // `a > b`, `b > c`, `c > 0`
        let chain = [
            Constraint::new(form(&[("a", 1), ("b", -1)], 0), true),
            Constraint::new(form(&[("b", 1), ("c", -1)], 0), true),
            Constraint::new(form(&[("c", 1)], 0), true),
        ];
        assert_eq!(signs(&form(&[("a", 1)], 0), &chain, &[]), SignSet::POSITIVE);
        assert_eq!(
            signs(&form(&[("a", 1), ("c", -1)], 0), &chain, &[]),
            SignSet::POSITIVE
        );
        assert_eq!(signs(&form(&[("a", 1)], -1), &chain, &[]), SignSet::ANY);
        let mut cycle = chain.to_vec();
        cycle.push(Constraint::new(form(&[("c", 1), ("a", -1)], 0), false));
        assert!(!feasible(&cycle, &[]));
    }

    #[test]
    fn disequalities() {
        // `a >= 0`, `a != 0`
        let constraints = [Constraint::new(form(&[("a", 1)], 0), false)];
        assert_eq!(
            signs(&form(&[("a", 1)], 0), &constraints, &[form(&[("a", 1)], 0)]),
            SignSet::POSITIVE
        );
        assert_eq!(
            signs(
                &form(&[("a", 1)], 0),
                &constraints,
                &[form(&[("a", 1)], -1)]
            ),
            SignSet::NONNEGATIVE
        );
    }
}
