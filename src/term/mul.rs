//! Product expression.

use std::fmt::Display;

use crate::{
    field::{Group, Ring, Set},
    printer::{PrettyPrint, PrettyPrinter, Print, PrintOptions},
    term::Normalize,
};

use super::{Flags, Term};

/// A product of expressions.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Mul<T: Set> {
    flags: u8,
    pub(crate) coefficient: <T::ProductCoefficientSet as Set>::Element,
    pub(crate) factors: Vec<Term<T>>,
    pub(crate) set: T,
}

impl<T: Set> Flags for Mul<T> {
    fn get_flags(&self) -> u8 {
        self.flags
    }
    fn get_flags_mut(&mut self) -> &mut u8 {
        &mut self.flags
    }
}

impl<T: Set> Mul<T> {
    /// Create a new product expression
    pub const fn new(
        coefficient: <T::ProductCoefficientSet as Set>::Element,
        factors: Vec<Term<T>>,
        ring: T,
    ) -> Self {
        Self {
            flags: 0,
            coefficient,
            factors,
            set: ring,
        }
    }
    /// Create a new empty product expression
    pub fn empty(ring: T) -> Self {
        Self::with_capacity(0, ring)
    }
    /// Create a new empty product, with an inner Vec with a defined capacity.
    pub fn with_capacity(capacity: usize, ring: T) -> Self {
        Self::new(
            ring.get_coefficient_set().nth(1),
            Vec::with_capacity(capacity),
            ring,
        )
    }
    /// Returns true if the multiplication is empty.
    pub const fn is_empty(&self) -> bool {
        self.factors.is_empty()
    }
    /// Get the number of terms in the product.
    pub fn len(&self) -> usize {
        self.factors.len() + usize::from(self.has_coeff())
    }
    /// Add a factor at the end of the product, without normalizing it
    pub fn push(&mut self, value: Term<T>) {
        self.set_normalized(false);
        self.factors.push(value);
    }
    /// Extend the product with another one, without normalizing it
    pub fn extend(&mut self, other: Self) {
        self.set_normalized(false);
        self.factors.extend(other.factors);
    }
    /// Return an iterator over the product factors.
    pub fn iter(&self) -> std::slice::Iter<'_, Term<T>> {
        self.factors.iter()
    }
    /// Checks if the product have a constant coefficient not equal to one.
    pub fn has_coeff(&self) -> bool {
        !self.set.get_coefficient_set().is_one(&self.coefficient)
    }
    /// Set the constant coefficient factor of the product
    pub fn set_coeff(&mut self, coeff: <T::ProductCoefficientSet as Set>::Element) {
        self.coefficient = coeff;
    }
}

impl<T: Set> Mul<T> {
    /// Return the constant coefficient factor of the product.
    pub fn get_coeff(&self) -> <T::ProductCoefficientSet as Set>::Element {
        self.coefficient.clone()
    }
    /// Return the constant coefficient factor of the product through a mutable reference.
    pub const fn get_coeff_mut(&mut self) -> &mut <T::ProductCoefficientSet as Set>::Element {
        &mut self.coefficient
    }
}

impl<T: Set> IntoIterator for Mul<T> {
    type Item = Term<T>;

    type IntoIter = std::vec::IntoIter<Term<T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.factors.into_iter()
    }
}

impl<'a, T: Set> IntoIterator for &'a Mul<T> {
    type Item = &'a Term<T>;

    type IntoIter = std::slice::Iter<'a, Term<T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.factors.iter()
    }
}

impl<T: Set> Print for Mul<T> {
    fn print(&self, options: &PrintOptions, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Print the coefficient at the beginning of the product, `-1` being printed as a minus sign
        if self.has_coeff() {
            let coefficient_set = self.set.get_coefficient_set();
            if coefficient_set.is_one(&coefficient_set.neg(&self.coefficient)) {
                Self::operator("-", options, f)?;
            } else {
                let is_sum = coefficient_set.is_sum(&self.coefficient);
                if is_sum {
                    Self::group_delim("(", options, f)?;
                }
                coefficient_set.print(&self.coefficient, options, f)?;
                if is_sum {
                    Self::group_delim(")", options, f)?;
                }
                Self::operator("*", options, f)?;
            }
        }
        for (i, factor) in self.factors.iter().enumerate() {
            if i != 0 {
                Self::operator("*", options, f)?;
            }
            Self::group(factor, options, f)?;
        }
        Ok(())
    }
}
impl<T: Set> Mul<T> {
    fn pretty_print_default<F: Fn() -> crate::printer::PrettyPrinter>(
        &self,
        f: F,
        options: &PrintOptions,
    ) -> crate::printer::PrettyPrinter {
        let mut den: Option<PrettyPrinter> = None;
        // Print the coefficient at the beginning of the product
        let mut num = if self.has_coeff() {
            let coefficient_set = self.set.get_coefficient_set();
            let mut coefficient = coefficient_set.pretty_print(&self.coefficient, options);
            if coefficient_set.is_sum(&self.coefficient) {
                coefficient.paren();
            }
            Some(coefficient)
        } else {
            None
        };
        for factor in &self.factors {
            let printed = match factor {
                Term::Pow(pow) if pow.exponant.is_strictly_negative() => {
                    let mut factor = pow.clone();
                    **factor.exponant = -&**factor.exponant;
                    &Term::Pow(factor).normalize()
                }
                _ => factor,
            };
            let mut elem = PrettyPrint::pretty_print(printed, options);
            if matches!(printed, Term::Add(_)) {
                elem.paren();
            }
            match factor {
                Term::Pow(pow) if pow.exponant.is_strictly_negative() => {
                    if let Some(den) = &mut den {
                        den.concat("⋅", false, &elem);
                    } else {
                        den = Some(elem);
                    }
                }
                _ => {
                    if let Some(num) = &mut num {
                        num.concat("⋅", false, &elem);
                    } else {
                        num = Some(elem);
                    }
                }
            }
        }

        let mut num = num.unwrap_or_else(f);
        if let Some(den) = den {
            num.vertical_concat("─", &den);
        }
        num
    }
}
impl<T: Set> PrettyPrint for Mul<T> {
    default fn pretty_print(&self, options: &PrintOptions) -> crate::printer::PrettyPrinter {
        self.pretty_print_default(|| unreachable!("Pretty printing a `Mul` in a set or a group should return a numerator. This is a bug, this product is not normalized or represents an impossible product (not living in a ring)"), options)
    }
}

impl<T: Ring> PrettyPrint for Mul<T> {
    fn pretty_print(&self, options: &PrintOptions) -> crate::printer::PrettyPrinter {
        self.pretty_print_default(
            || PrettyPrint::pretty_print(&Term::one(self.set), options),
            options,
        )
    }
}

impl<T: Set> Display for Mul<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        PrettyPrint::fmt(self, &PrintOptions::default(), f)
    }
}
