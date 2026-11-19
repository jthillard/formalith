//! Relations between two expressions, like `x < 1`, used as conditions of `piecewise` and as inequalities.
//!
//! In a `piecewise`, a condition `lhs < rhs` is the internal function `@lt(lhs, rhs)`, which is never evaluated.

use crate::{
    context::{Symbol, assumptions::SignSet},
    parser::lexer::TokenKind,
};

/// A comparison `lhs op rhs`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Relation {
    /// `lhs < rhs`
    Less,
    /// `lhs <= rhs`
    LessEqual,
    /// `lhs > rhs`
    Greater,
    /// `lhs >= rhs`
    GreaterEqual,
    /// `lhs = rhs`
    Equal,
    /// `lhs != rhs`
    NotEqual,
}

impl Relation {
    /// Every relation.
    pub const ALL: [Self; 6] = [
        Self::Less,
        Self::LessEqual,
        Self::Greater,
        Self::GreaterEqual,
        Self::Equal,
        Self::NotEqual,
    ];

    /// The relation of a comparison token, like `<`.
    #[must_use]
    pub const fn from_token(token: &TokenKind) -> Option<Self> {
        Some(match token {
            TokenKind::Less => Self::Less,
            TokenKind::LessEqual => Self::LessEqual,
            TokenKind::Greater => Self::Greater,
            TokenKind::GreaterEqual => Self::GreaterEqual,
            TokenKind::Equal => Self::Equal,
            TokenKind::NotEqual => Self::NotEqual,
            _ => return None,
        })
    }

    /// The internal function standing for the relation in conditions, like `@lt`.
    #[must_use]
    pub fn symbol(self) -> Symbol {
        Symbol::new(match self {
            Self::Less => "@lt",
            Self::LessEqual => "@le",
            Self::Greater => "@gt",
            Self::GreaterEqual => "@ge",
            Self::Equal => "@eq",
            Self::NotEqual => "@ne",
        })
    }

    /// The relation whose internal function is `symbol`.
    #[must_use]
    pub fn from_symbol(symbol: Symbol) -> Option<Self> {
        Self::ALL
            .into_iter()
            .find(|relation| relation.symbol() == symbol)
    }

    /// The operator, like `<=`.
    #[must_use]
    pub const fn operator(self) -> &'static str {
        match self {
            Self::Less => "<",
            Self::LessEqual => "<=",
            Self::Greater => ">",
            Self::GreaterEqual => ">=",
            Self::Equal => "=",
            Self::NotEqual => "!=",
        }
    }

    /// The operator, printed in the pretty printer, like `≤`.
    #[must_use]
    pub const fn pretty_operator(self) -> &'static str {
        match self {
            Self::LessEqual => "≤",
            Self::GreaterEqual => "≥",
            Self::NotEqual => "≠",
            _ => self.operator(),
        }
    }

    /// The signs of `lhs - rhs` for which the relation holds.
    #[must_use]
    pub const fn signs(self) -> SignSet {
        match self {
            Self::Less => SignSet::NEGATIVE,
            Self::LessEqual => SignSet::NONPOSITIVE,
            Self::Greater => SignSet::POSITIVE,
            Self::GreaterEqual => SignSet::NONNEGATIVE,
            Self::Equal => SignSet::ZERO,
            Self::NotEqual => SignSet::NONZERO,
        }
    }

    /// Whether the relation holds when `lhs - rhs` has one of the signs `signs`, `None` if it depends on the sign.
    #[must_use]
    pub const fn holds(self, signs: SignSet) -> Option<bool> {
        if signs.is_subset(self.signs()) {
            Some(true)
        } else if signs.is_disjoint(self.signs()) {
            Some(false)
        } else {
            None
        }
    }
}
