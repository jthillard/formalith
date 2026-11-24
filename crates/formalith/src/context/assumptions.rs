//! Assumptions on symbols, like `a > 0` or `n` integer, declared with `assume(...)`.
//!
//! Assumptions are stored in an [`Environment`](crate::parser::environment::Environment), and made current for the
//! thread while it evaluates an input ([`Assumptions::enter`]), so that normalization, limits, integrals and solving
//! can query them with [`assumption`].

use std::{cell::RefCell, cmp::Ordering, collections::BTreeMap, fmt};

use super::Symbol;

/// A set of possible signs, among negative, zero and positive.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
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

/// What is assumed of a symbol.
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

    /// The assumption written as conditions on `name`, like `n > 0` and `n integer` (`n in ZZ` in Typst).
    #[must_use]
    pub fn describe(&self, name: &str, typst: bool) -> Vec<String> {
        let relation = match self.sign {
            SignSet::NEGATIVE => Some("< 0"),
            SignSet::ZERO => Some("= 0"),
            SignSet::POSITIVE => Some("> 0"),
            SignSet::NONPOSITIVE => Some("<= 0"),
            SignSet::NONNEGATIVE => Some(">= 0"),
            SignSet::NONZERO => Some("!= 0"),
            _ => None,
        };
        let mut res: Vec<String> = relation
            .map(|r| format!("{name} {r}"))
            .into_iter()
            .collect();
        if self.integer {
            res.push(if typst {
                format!("{name} in ZZ")
            } else {
                format!("{name} integer")
            });
        }
        res
    }
}

impl Default for Assumption {
    fn default() -> Self {
        Self::NONE
    }
}

/// Assumptions on symbols.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Assumptions(BTreeMap<Symbol, Assumption>);

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
        Self(
            ["k", "m", "n"]
                .into_iter()
                .map(|name| (Symbol::new(name), Assumption::INTEGER))
                .collect(),
        )
    }

    /// The assumptions of `self` that aren't in `other`, or differ from those of `other`.
    #[must_use]
    pub fn difference(&self, other: &Self) -> Self {
        Self(
            self.0
                .iter()
                .filter(|(symbol, assumption)| other.0.get(symbol) != Some(assumption))
                .map(|(symbol, assumption)| (*symbol, *assumption))
                .collect(),
        )
    }

    /// The assumption on `symbol`.
    #[must_use]
    pub fn get(&self, symbol: Symbol) -> Assumption {
        self.0.get(&symbol).copied().unwrap_or_default()
    }

    /// Add `assumption` on `symbol` to the existing ones.
    ///
    /// # Errors
    /// Returns an error message if it contradicts the existing assumptions.
    pub fn assume(&mut self, symbol: Symbol, assumption: Assumption) -> Result<(), String> {
        let res = self.get(symbol).and(assumption).ok_or_else(|| {
            format!(
                "this contradicts {}",
                self.get(symbol).describe(symbol.name(), false).join(", ")
            )
        })?;
        self.0.insert(symbol, res);
        Ok(())
    }

    /// Remove the assumptions on `symbol`, returning whether there were some.
    pub fn remove(&mut self, symbol: Symbol) -> bool {
        self.0.remove(&symbol).is_some()
    }

    /// Remove every assumption.
    pub fn clear(&mut self) {
        self.0.clear();
    }

    /// Whether there is no assumption.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Iterate over the symbols with assumptions.
    pub fn iter(&self) -> impl Iterator<Item = (Symbol, Assumption)> + '_ {
        self.0
            .iter()
            .map(|(symbol, assumption)| (*symbol, *assumption))
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

    /// The assumptions as comma-separated conditions sorted by symbol name, like `a > 0, n integer`, or in Typst.
    #[must_use]
    pub fn describe(&self, typst: bool) -> String {
        let mut symbols: Vec<_> = self.iter().collect();
        symbols.sort_by_key(|(symbol, _)| symbol.name());
        let conditions: Vec<String> = symbols
            .into_iter()
            .flat_map(|(symbol, assumption)| assumption.describe(symbol.name(), typst))
            .collect();
        conditions.join(", ")
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
