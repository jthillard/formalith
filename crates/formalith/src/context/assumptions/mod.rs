//! Assumptions on symbols, like `a > 0`, `a > b + 1` or `n` integer, declared with `assume(...)`.
//!
//! Assumptions are stored in an [`Environment`](crate::parser::environment::Environment), and made current for the
//! thread while it evaluates an input ([`Assumptions::enter`]), so that normalization, limits, integrals and solving
//! can query them with [`assumption`].

pub mod linear;

use std::{
    cell::RefCell,
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use linear::{Constraint, LinearForm, Var};
use malachite::{
    Rational,
    base::num::{
        arithmetic::traits::{Ceiling, Floor, Sign},
        basic::traits::One,
    },
};

use super::Symbol;

/// A set of possible signs, among negative, zero and positive.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SignSet(u8);

impl SignSet {
    const NEG: u8 = 1;
    const ZERO_BIT: u8 = 2;
    const POS: u8 = 4;

    /// No possible sign, a contradiction.
    pub const EMPTY: Self = Self(0);
    /// Negative.
    pub const NEGATIVE: Self = Self(Self::NEG);
    /// Zero.
    pub const ZERO: Self = Self(Self::ZERO_BIT);
    /// Positive.
    pub const POSITIVE: Self = Self(Self::POS);
    /// Negative or zero.
    pub const NONPOSITIVE: Self = Self(Self::NEG | Self::ZERO_BIT);
    /// Positive or zero.
    pub const NONNEGATIVE: Self = Self(Self::POS | Self::ZERO_BIT);
    /// Negative or positive.
    pub const NONZERO: Self = Self(Self::NEG | Self::POS);
    /// Any sign.
    pub const ANY: Self = Self(Self::NEG | Self::ZERO_BIT | Self::POS);

    /// The set made of a single sign.
    #[must_use]
    pub const fn from_ordering(sign: Ordering) -> Self {
        match sign {
            Ordering::Less => Self::NEGATIVE,
            Ordering::Equal => Self::ZERO,
            Ordering::Greater => Self::POSITIVE,
        }
    }

    /// The sign, when it is known.
    #[must_use]
    pub const fn strict(self) -> Option<Ordering> {
        match self.0 {
            Self::NEG => Some(Ordering::Less),
            Self::ZERO_BIT => Some(Ordering::Equal),
            Self::POS => Some(Ordering::Greater),
            _ => None,
        }
    }

    /// Whether every sign of `self` is in `other`.
    #[must_use]
    pub const fn is_subset(self, other: Self) -> bool {
        self.0 & !other.0 == 0
    }

    /// Whether the sets have no sign in common.
    #[must_use]
    pub const fn is_disjoint(self, other: Self) -> bool {
        self.0 & other.0 == 0
    }

    /// The signs in both sets.
    #[must_use]
    pub const fn intersect(self, other: Self) -> Self {
        Self(self.0 & other.0)
    }

    /// The signs in either set.
    #[must_use]
    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    /// Whether `self` contains the sign `sign`.
    #[must_use]
    pub const fn contains(self, sign: Ordering) -> bool {
        !Self::from_ordering(sign).is_disjoint(self)
    }

    /// The signs not in `self`.
    #[must_use]
    pub const fn complement(self) -> Self {
        Self(!self.0 & Self::ANY.0)
    }

    /// The signs of `-u` for `u` with signs in `self`.
    #[must_use]
    pub const fn neg(self) -> Self {
        Self((self.0 & Self::ZERO_BIT) | ((self.0 & Self::NEG) << 2) | ((self.0 & Self::POS) >> 2))
    }
}

/// The signs of a product `u v`.
impl std::ops::Mul for SignSet {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        let mut res = Self::EMPTY;
        for a in [Ordering::Less, Ordering::Equal, Ordering::Greater] {
            for b in [Ordering::Less, Ordering::Equal, Ordering::Greater] {
                if self.contains(a) && other.contains(b) {
                    let sign = match (a, b) {
                        (Ordering::Equal, _) | (_, Ordering::Equal) => Ordering::Equal,
                        _ if a == b => Ordering::Greater,
                        _ => Ordering::Less,
                    };
                    res = res.union(Self::from_ordering(sign));
                }
            }
        }
        res
    }
}

/// The signs of a sum `u + v`.
impl std::ops::Add for SignSet {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let mut res = Self::EMPTY;
        for a in [Ordering::Less, Ordering::Equal, Ordering::Greater] {
            for b in [Ordering::Less, Ordering::Equal, Ordering::Greater] {
                if self.contains(a) && other.contains(b) {
                    res = res.union(match (a, b) {
                        (Ordering::Equal, s) | (s, Ordering::Equal) => Self::from_ordering(s),
                        _ if a == b => Self::from_ordering(a),
                        _ => Self::ANY,
                    });
                }
            }
        }
        res
    }
}

/// What is assumed of a symbol, as implied by every assumption.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Assumption {
    /// Its possible signs.
    pub sign: SignSet,
    /// Whether it is an integer.
    pub integer: bool,
}

impl Assumption {
    /// No assumption.
    pub const NONE: Self = Self {
        sign: SignSet::ANY,
        integer: false,
    };
    /// The assumption that a symbol is an integer.
    pub const INTEGER: Self = Self {
        sign: SignSet::ANY,
        integer: true,
    };

    /// The assumption that a symbol has a sign in `sign`.
    #[must_use]
    pub const fn sign(sign: SignSet) -> Self {
        Self {
            sign,
            integer: false,
        }
    }

    /// Both assumptions, `None` if they contradict each other.
    #[must_use]
    pub const fn and(self, other: Self) -> Option<Self> {
        let sign = self.sign.intersect(other.sign);
        if sign.0 == SignSet::EMPTY.0 {
            return None;
        }
        Some(Self {
            sign,
            integer: self.integer || other.integer,
        })
    }
}

impl Default for Assumption {
    fn default() -> Self {
        Self::NONE
    }
}

/// A bound of a symbol.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Bound {
    value: Rational,
    strict: bool,
}

impl Bound {
    /// The stronger of two lower bounds (`lower`) or of two upper bounds.
    fn stronger(a: Option<Self>, b: Option<Self>, lower: bool) -> Option<Self> {
        match (a, b) {
            (Some(a), Some(b)) => Some(match a.value.cmp(&b.value) {
                Ordering::Equal => Self {
                    strict: a.strict || b.strict,
                    ..a
                },
                Ordering::Greater if lower => a,
                Ordering::Less if !lower => a,
                _ => b,
            }),
            (a, b) => a.or(b),
        }
    }
}

/// What is assumed of a single symbol: bounds, excluded values, being an integer.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Declared {
    lower: Option<Bound>,
    upper: Option<Bound>,
    excluded: BTreeSet<Rational>,
    integer: bool,
}

impl Declared {
    /// Both, tightened.
    fn and(&self, other: &Self) -> Self {
        let mut res = Self {
            lower: Bound::stronger(self.lower.clone(), other.lower.clone(), true),
            upper: Bound::stronger(self.upper.clone(), other.upper.clone(), false),
            excluded: self.excluded.union(&other.excluded).cloned().collect(),
            integer: self.integer || other.integer,
        };
        res.tighten();
        res
    }

    /// Integer bounds for integers, excluded values at a bound making it strict, excluded values out of the bounds
    /// dropped.
    fn tighten(&mut self) {
        loop {
            if self.integer {
                if let Some(lower) = &mut self.lower {
                    let ceiling = Rational::from((&lower.value).ceiling());
                    lower.value = if lower.strict && ceiling == lower.value {
                        ceiling + Rational::ONE
                    } else {
                        ceiling
                    };
                    lower.strict = false;
                }
                if let Some(upper) = &mut self.upper {
                    let floor = Rational::from((&upper.value).floor());
                    upper.value = if upper.strict && floor == upper.value {
                        floor - Rational::ONE
                    } else {
                        floor
                    };
                    upper.strict = false;
                }
                self.excluded.retain(|p| p.denominator_ref() == &1u32);
            }
            let mut changed = false;
            for bound in [&mut self.lower, &mut self.upper].into_iter().flatten() {
                if !bound.strict && self.excluded.contains(&bound.value) {
                    bound.strict = true;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        let (lower, upper) = (&self.lower, &self.upper);
        self.excluded.retain(|p| {
            lower.as_ref().is_none_or(|b| *p > b.value)
                && upper.as_ref().is_none_or(|b| *p < b.value)
        });
    }

    /// Whether no value satisfies it.
    fn is_empty(&self) -> bool {
        match (&self.lower, &self.upper) {
            (Some(lower), Some(upper)) => match lower.value.cmp(&upper.value) {
                Ordering::Greater => true,
                Ordering::Equal => lower.strict || upper.strict,
                Ordering::Less => false,
            },
            _ => false,
        }
    }

    /// `x - p` has a sign in `signs`.
    fn of_sign(p: &Rational, signs: SignSet) -> Self {
        let bound = |strict| {
            Some(Bound {
                value: p.clone(),
                strict,
            })
        };
        let mut res = Self::default();
        match signs {
            SignSet::POSITIVE => res.lower = bound(true),
            SignSet::NONNEGATIVE => res.lower = bound(false),
            SignSet::NEGATIVE => res.upper = bound(true),
            SignSet::NONPOSITIVE => res.upper = bound(false),
            SignSet::ZERO => {
                res.lower = bound(false);
                res.upper = bound(false);
            }
            SignSet::NONZERO => {
                res.excluded.insert(p.clone());
            }
            SignSet::EMPTY => {
                res.lower = bound(true);
                res.upper = bound(true);
            }
            _ => {}
        }
        res
    }

    /// The conditions on `x`, as forms with the signs they have: `{$x - p > 0$}` for a lower bound `p`...
    fn conditions(&self, x: Symbol) -> Vec<(LinearForm, SignSet)> {
        let at = |p: &Rational| {
            let mut form = LinearForm::variable(Var::Symbol(x));
            form.constant = -p;
            form
        };
        let mut res = vec![];
        if let (Some(lower), Some(upper)) = (&self.lower, &self.upper)
            && lower.value == upper.value
        {
            res.push((at(&lower.value), SignSet::ZERO));
        } else {
            for (bound, sign) in [
                (&self.lower, SignSet::POSITIVE),
                (&self.upper, SignSet::NEGATIVE),
            ] {
                if let Some(bound) = bound {
                    let signs = if bound.strict {
                        sign
                    } else {
                        sign.union(SignSet::ZERO)
                    };
                    res.push((at(&bound.value), signs));
                }
            }
        }
        res.extend(self.excluded.iter().map(|p| (at(p), SignSet::NONZERO)));
        res
    }

    /// Whether it says more than the sign of the symbol.
    fn is_relational(&self) -> bool {
        [&self.lower, &self.upper]
            .into_iter()
            .flatten()
            .any(|bound| bound.value != 0)
            || self.excluded.iter().any(|p| *p != 0)
    }
}

/// A relation `{$f in S$}` between several symbols, with `S` among positive, non-negative, zero and non-zero, and
/// `f` with coprime integer coefficients (the first one positive for zero and non-zero).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct LinearRelation {
    form: LinearForm,
    signs: SignSet,
}

impl LinearRelation {
    /// The canonical relation `{$f in S$}`, `None` for any sign.
    fn new(form: &LinearForm, signs: SignSet) -> Option<Self> {
        let (form, signs) = if signs == SignSet::NEGATIVE || signs == SignSet::NONPOSITIVE {
            (form.neg(), signs.neg())
        } else if (signs == SignSet::ZERO || signs == SignSet::NONZERO)
            && form.coefficients.values().next().is_some_and(|c| *c < 0)
        {
            (form.neg(), signs)
        } else {
            (form.clone(), signs)
        };
        (signs != SignSet::ANY).then(|| Self {
            form: form.primitive(),
            signs,
        })
    }

    fn mentions(&self, symbol: Symbol) -> bool {
        self.form.coefficients.contains_key(&Var::Symbol(symbol))
    }

    /// The name of its first symbol by name, to sort relations.
    fn first_name(&self) -> &'static str {
        self.form
            .symbols()
            .map(Symbol::name)
            .min()
            .unwrap_or_default()
    }
}

/// Assumptions on symbols: bounds, excluded values and being an integer for each symbol, and linear relations with
/// rational coefficients between symbols, like `{$a > b + 1$}`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Assumptions {
    symbols: BTreeMap<Symbol, Declared>,
    relations: BTreeSet<LinearRelation>,
    /// The assumption on each symbol implied by every assumption, see [`Assumptions::refresh`].
    derived: BTreeMap<Symbol, Assumption>,
    /// Every assumption as constraints and disequalities.
    constraints: Vec<Constraint>,
    disequalities: Vec<LinearForm>,
    /// The symbols with conditions other than on their sign.
    relational: BTreeSet<Symbol>,
}

thread_local! {
    /// The assumptions in use on this thread, see [`Assumptions::enter`].
    static CURRENT: RefCell<Assumptions> = RefCell::default();
}

/// Restores the previous assumptions of the thread when dropped, see [`Assumptions::enter`].
#[must_use = "the assumptions are only in use until the guard is dropped"]
pub struct AssumptionsGuard {
    previous: Option<Assumptions>,
}

impl Drop for AssumptionsGuard {
    fn drop(&mut self) {
        if let Some(previous) = self.previous.take() {
            CURRENT.with_borrow_mut(|current| *current = previous);
        }
    }
}

impl Assumptions {
    /// No assumption.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// The assumptions sessions start with: `k`, `m` and `n` are integers.
    #[must_use]
    pub fn defaults() -> Self {
        let mut res = Self::new();
        for name in ["k", "m", "n"] {
            res.symbols.entry(Symbol::new(name)).or_default().integer = true;
        }
        res.refresh();
        res
    }

    /// The assumptions of `self` that aren't in `other`, or differ from those of `other`.
    #[must_use]
    pub fn difference(&self, other: &Self) -> Self {
        let mut res = Self {
            symbols: self
                .symbols
                .iter()
                .filter(|(symbol, declared)| other.symbols.get(symbol) != Some(declared))
                .map(|(symbol, declared)| (*symbol, declared.clone()))
                .collect(),
            relations: self
                .relations
                .difference(&other.relations)
                .cloned()
                .collect(),
            ..Self::default()
        };
        res.refresh();
        res
    }

    /// The assumptions mentioning one of `symbols`: theirs, and the relations involving them.
    #[must_use]
    pub fn restrict(&self, symbols: &BTreeSet<Symbol>) -> Self {
        let mut res = Self {
            symbols: self
                .symbols
                .iter()
                .filter(|(symbol, _)| symbols.contains(symbol))
                .map(|(symbol, declared)| (*symbol, declared.clone()))
                .collect(),
            relations: self
                .relations
                .iter()
                .filter(|relation| symbols.iter().any(|s| relation.mentions(*s)))
                .cloned()
                .collect(),
            ..Self::default()
        };
        res.refresh();
        res
    }

    /// The assumption on `symbol` implied by every assumption.
    #[must_use]
    pub fn get(&self, symbol: Symbol) -> Assumption {
        self.derived.get(&symbol).copied().unwrap_or_default()
    }

    /// Add `assumption` on `symbol` to the existing ones.
    ///
    /// # Errors
    /// Returns an error message if it contradicts the existing assumptions.
    pub fn assume(&mut self, symbol: Symbol, assumption: Assumption) -> Result<(), String> {
        self.update(&[symbol], |res| {
            if assumption.integer {
                res.symbols.entry(symbol).or_default().integer = true;
            }
            res.add_relation(&LinearForm::variable(Var::Symbol(symbol)), assumption.sign);
        })
    }

    /// Add the assumption that `symbol` is an integer.
    ///
    /// # Errors
    /// Returns an error message if it contradicts the existing assumptions, like `{$1/3 < n < 2/3$}`.
    pub fn assume_integer(&mut self, symbol: Symbol) -> Result<(), String> {
        self.assume(symbol, Assumption::INTEGER)
    }

    /// Add the assumption that `form` has a sign in `signs`, `form` having only symbols as variables.
    ///
    /// # Errors
    /// Returns an error message if it contradicts the existing assumptions.
    pub fn assume_relation(&mut self, form: &LinearForm, signs: SignSet) -> Result<(), String> {
        let symbols: Vec<Symbol> = form.symbols().collect();
        self.update(&symbols, |res| res.add_relation(form, signs))
    }

    /// Add every assumption of `other`.
    ///
    /// # Errors
    /// Returns an error message if they contradict the existing assumptions.
    pub fn merge(&mut self, other: &Self) -> Result<(), String> {
        let symbols: BTreeSet<Symbol> = other
            .symbols
            .keys()
            .copied()
            .chain(other.relations.iter().flat_map(|r| r.form.symbols()))
            .collect();
        let symbols: Vec<Symbol> = symbols.into_iter().collect();
        self.update(&symbols, |res| {
            for (symbol, declared) in &other.symbols {
                let entry = res.symbols.entry(*symbol).or_default();
                *entry = entry.and(declared);
            }
            res.relations.extend(other.relations.iter().cloned());
        })
    }

    /// Apply `change`, unless the result is contradictory, `symbols` being the symbols it involves.
    fn update(&mut self, symbols: &[Symbol], change: impl FnOnce(&mut Self)) -> Result<(), String> {
        let mut res = self.clone();
        change(&mut res);
        if res.refresh() {
            *self = res;
            return Ok(());
        }
        let involved = self.restrict(&symbols.iter().copied().collect());
        Err(if involved.is_empty() {
            "this is contradictory".to_owned()
        } else {
            format!("this contradicts {}", involved.describe(false))
        })
    }

    /// Add `{$f in S$}` without checking it.
    fn add_relation(&mut self, form: &LinearForm, signs: SignSet) {
        let mut symbols = form.symbols();
        match (symbols.next(), symbols.next()) {
            (None, _) => {
                if !signs.contains(form.constant.sign()) {
                    // A contradiction, found by `refresh`
                    self.relations.insert(LinearRelation {
                        form: LinearForm::constant(-Rational::ONE),
                        signs: SignSet::NONNEGATIVE,
                    });
                }
            }
            (Some(x), None) => {
                // `c x + d in S` is `x - p in S` (or `-S` for `c < 0`) with `p = -d/c`
                let c = form.coefficient(Var::Symbol(x));
                let signs = if c < 0 { signs.neg() } else { signs };
                let declared = Declared::of_sign(&(-&form.constant / c), signs);
                let entry = self.symbols.entry(x).or_default();
                *entry = entry.and(&declared);
            }
            _ => {
                if let Some(relation) = LinearRelation::new(form, signs) {
                    self.relations.insert(relation);
                }
            }
        }
    }

    /// Compute the derived data from the assumptions, returning whether they are consistent.
    fn refresh(&mut self) -> bool {
        self.symbols
            .retain(|_, declared| *declared != Declared::default());
        let mut conditions: Vec<(LinearForm, SignSet)> = self
            .symbols
            .iter()
            .flat_map(|(symbol, declared)| declared.conditions(*symbol))
            .collect();
        conditions.extend(self.relations.iter().map(|r| (r.form.clone(), r.signs)));
        self.constraints.clear();
        self.disequalities.clear();
        for (form, signs) in conditions {
            match signs {
                SignSet::POSITIVE => self.constraints.push(Constraint::new(form, true)),
                SignSet::NONNEGATIVE => self.constraints.push(Constraint::new(form, false)),
                SignSet::NEGATIVE => self.constraints.push(Constraint::new(form.neg(), true)),
                SignSet::NONPOSITIVE => self.constraints.push(Constraint::new(form.neg(), false)),
                SignSet::ZERO => {
                    self.constraints.push(Constraint::new(form.neg(), false));
                    self.constraints.push(Constraint::new(form, false));
                }
                SignSet::NONZERO => self.disequalities.push(form),
                _ => {}
            }
        }
        if self.symbols.values().any(Declared::is_empty)
            || !linear::feasible(&self.constraints, &self.disequalities)
        {
            return false;
        }
        self.relational = self
            .symbols
            .iter()
            .filter(|(_, declared)| declared.is_relational())
            .map(|(symbol, _)| *symbol)
            .chain(self.relations.iter().flat_map(|r| r.form.symbols()))
            .collect();
        let symbols: BTreeSet<Symbol> = self
            .symbols
            .keys()
            .copied()
            .chain(self.relational.iter().copied())
            .collect();
        self.derived = symbols
            .into_iter()
            .map(|symbol| {
                let sign = linear::signs(
                    &LinearForm::variable(Var::Symbol(symbol)),
                    &self.constraints,
                    &self.disequalities,
                );
                let integer = self.symbols.get(&symbol).is_some_and(|d| d.integer);
                (symbol, Assumption { sign, integer })
            })
            .collect();
        true
    }

    /// Remove the assumptions on `symbol`, and the relations involving it, returning whether there were some.
    pub fn remove(&mut self, symbol: Symbol) -> bool {
        let count = self.symbols.len() + self.relations.len();
        self.symbols.remove(&symbol);
        self.relations.retain(|relation| !relation.mentions(symbol));
        let removed = count != self.symbols.len() + self.relations.len();
        self.refresh();
        removed
    }

    /// Remove every assumption.
    pub fn clear(&mut self) {
        *self = Self::new();
    }

    /// Whether there is no assumption.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.symbols.is_empty() && self.relations.is_empty()
    }

    /// The conditions involving `symbol`, as forms with the signs they have, like `{$x - 1 > 0$}` for `{$x > 1$}`.
    #[must_use]
    pub fn conditions_on(&self, symbol: Symbol) -> Vec<(LinearForm, SignSet)> {
        let mut res = self
            .symbols
            .get(&symbol)
            .map_or_else(Vec::new, |declared| declared.conditions(symbol));
        res.extend(
            self.relations
                .iter()
                .filter(|relation| relation.mentions(symbol))
                .map(|relation| (relation.form.clone(), relation.signs)),
        );
        res
    }

    /// The possible signs of `form` under these assumptions and the `extra` constraints.
    #[must_use]
    pub fn signs(&self, form: &LinearForm, extra: &[Constraint]) -> SignSet {
        let mut constraints = self.constraints.clone();
        constraints.extend_from_slice(extra);
        linear::signs(form, &constraints, &self.disequalities)
    }

    /// Whether `symbol` has conditions other than on its sign, like `{$a > 1$}` or `{$a > b$}`.
    #[must_use]
    pub fn is_relational(&self, symbol: Symbol) -> bool {
        self.relational.contains(&symbol)
    }

    /// The assumptions currently in use on this thread, see [`Assumptions::enter`].
    #[must_use]
    pub fn current() -> Self {
        CURRENT.with_borrow(Clone::clone)
    }

    /// Use these assumptions on this thread until the returned guard is dropped, which restores the previous ones.
    pub fn enter(&self) -> AssumptionsGuard {
        let previous = CURRENT.with_borrow_mut(|current| std::mem::replace(current, self.clone()));
        AssumptionsGuard {
            previous: Some(previous),
        }
    }

    /// The assumptions on each symbol sorted by name, then the relations, as conditions like `a > 1` and
    /// `n integer`, or in Typst.
    fn lines(&self, typst: bool) -> Vec<(Option<Symbol>, Vec<String>)> {
        let mut symbols: Vec<_> = self.symbols.iter().collect();
        symbols.sort_by_key(|(symbol, _)| symbol.name());
        let mut relations: Vec<_> = self.relations.iter().collect();
        relations.sort_by_key(|relation| relation.first_name());
        symbols
            .into_iter()
            .map(|(symbol, declared)| {
                let mut conditions: Vec<String> = declared
                    .conditions(*symbol)
                    .iter()
                    .map(|(form, signs)| print::relation(form, *signs, typst))
                    .collect();
                if declared.integer {
                    conditions.push(if typst {
                        format!("{} in ZZ", print::symbol(*symbol, true))
                    } else {
                        format!("{} integer", print::symbol(*symbol, false))
                    });
                }
                (Some(*symbol), conditions)
            })
            .chain(
                relations
                    .into_iter()
                    .map(|r| (None, vec![print::relation(&r.form, r.signs, typst)])),
            )
            .collect()
    }

    /// The assumptions as comma-separated conditions, those on each symbol sorted by name then the relations, like
    /// `a > 1, n integer, a > b`, or in Typst.
    #[must_use]
    pub fn describe(&self, typst: bool) -> String {
        self.lines(typst)
            .into_iter()
            .flat_map(|(_, conditions)| conditions)
            .collect::<Vec<_>>()
            .join(", ")
    }

    /// The assumptions, one line per symbol sorted by name then one per relation, those on symbols equal to their
    /// assumptions in `defaults` followed by `(default)`.
    #[must_use]
    pub fn listing(&self, defaults: &Self) -> Vec<String> {
        self.lines(false)
            .into_iter()
            .map(|(symbol, conditions)| {
                let line = conditions.join(", ");
                if symbol.is_some_and(|s| defaults.symbols.get(&s) == self.symbols.get(&s)) {
                    format!("{line} (default)")
                } else {
                    line
                }
            })
            .collect()
    }
}

impl fmt::Display for Assumptions {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.describe(false))
    }
}

/// The assumption on `symbol` currently in use on this thread, see [`Assumptions::enter`].
#[must_use]
pub fn assumption(symbol: Symbol) -> Assumption {
    CURRENT.with_borrow(|current| current.get(symbol))
}

/// Whether `symbol` currently has conditions other than on its sign, see [`Assumptions::is_relational`].
#[must_use]
pub fn is_relational(symbol: Symbol) -> bool {
    CURRENT.with_borrow(|current| current.is_relational(symbol))
}

/// The possible signs of `form` under the current assumptions and the `extra` constraints.
#[must_use]
pub fn linear_signs(form: &LinearForm, extra: &[Constraint]) -> SignSet {
    CURRENT.with_borrow(|current| current.signs(form, extra))
}

/// Printing of conditions as real expressions, so that they parse back.
mod print {
    use malachite::Rational;

    use super::{LinearForm, SignSet, Var};
    use crate::{
        context::Symbol,
        field::commons::real::expr::{Expr, value, variable},
        printer::{Print, PrintOptions},
    };

    fn print(term: &Expr, typst: bool) -> String {
        let options = if typst {
            PrintOptions::typst()
        } else {
            PrintOptions::plain()
        };
        term.with_options(options).to_string()
    }

    /// `symbol` as printed in an expression.
    pub(super) fn symbol(symbol: Symbol, typst: bool) -> String {
        print(&variable(symbol), typst)
    }

    /// `{$f in S$}` as a relation with the symbols of positive coefficients on the left, like `a + 2 b > c + 1`, or
    /// those of negative coefficients when there are none, like `a + b < 3`.
    pub(super) fn relation(form: &LinearForm, signs: SignSet, typst: bool) -> String {
        let (mut left, mut right) = (value(Rational::from(0)), value(-&form.constant));
        for (x, c) in &form.coefficients {
            let Var::Symbol(s) = x else { continue };
            if *c > 0 {
                left += value(c.clone()) * variable(*s);
            } else {
                right += value(-c) * variable(*s);
            }
        }
        let mut operator = match signs {
            SignSet::POSITIVE => ">",
            SignSet::NONNEGATIVE => ">=",
            SignSet::NEGATIVE => "<",
            SignSet::NONPOSITIVE => "<=",
            SignSet::ZERO => "=",
            _ => "!=",
        };
        if left.is_zero() {
            // `0 > g - c` is `g < c`
            (left, right) = (
                right + value(form.constant.clone()),
                value(form.constant.clone()),
            );
            operator = match operator {
                ">" => "<",
                ">=" => "<=",
                "<" => ">",
                "<=" => ">=",
                operator => operator,
            };
        }
        format!(
            "{} {operator} {}",
            print(&left, typst),
            print(&right, typst)
        )
    }
}
