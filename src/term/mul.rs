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
    /// Print the coefficient, as a decimal number if it is a numerical approximation.
    fn print_coefficient_element(
        &self,
        options: &PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        let coefficient_set = self.set.get_coefficient_set();
        if self.is_approximate() {
            coefficient_set.print_approximate(&self.coefficient, options, f)
        } else {
            coefficient_set.print(&self.coefficient, options, f)
        }
    }
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

impl<T: Set> Mul<T> {
    /// Print the product as typst source, factors with a negative exponent going to a `frac` denominator.
    fn print_typst(
        &self,
        options: &PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        let mut num = vec![];
        let mut den = vec![];
        for factor in &self.factors {
            match factor {
                Term::Pow(pow) if pow.exponant.is_strictly_negative() => {
                    let mut factor = pow.clone();
                    **factor.exponant = -&**factor.exponant;
                    den.push(Term::Pow(factor).normalize());
                }
                _ => num.push(factor.clone()),
            }
        }
        let print_factors = |factors: &[Term<T>], f: &mut std::fmt::Formatter<'_>| {
            for (i, factor) in factors.iter().enumerate() {
                if i != 0 {
                    Self::mul_sign(options, f)?;
                }
                if matches!(factor, Term::Add(_)) {
                    Self::group(factor, options, f)?;
                } else {
                    Print::print(factor, options, f)?;
                }
            }
            Ok(())
        };
        let print_coefficient = |f: &mut std::fmt::Formatter<'_>| {
            let coefficient_set = self.set.get_coefficient_set();
            let is_sum = coefficient_set.is_sum(&self.coefficient);
            if is_sum {
                Self::group_delim("(", options, f)?;
            }
            self.print_coefficient_element(options, f)?;
            if is_sum {
                Self::group_delim(")", options, f)?;
            }
            Ok(())
        };

        let coefficient_set = self.set.get_coefficient_set();
        let minus_one =
            self.has_coeff() && coefficient_set.is_one(&coefficient_set.neg(&self.coefficient));
        if minus_one {
            Self::operator("-", options, f)?;
        }
        if den.is_empty() {
            if self.has_coeff() && !minus_one {
                print_coefficient(f)?;
                if !num.is_empty() {
                    Self::mul_sign(options, f)?;
                }
            }
            return print_factors(&num, f);
        }
        if self.has_coeff() && !minus_one && !num.is_empty() {
            print_coefficient(f)?;
            Self::mul_sign(options, f)?;
        }
        f.write_str("frac(")?;
        if num.is_empty() {
            if self.has_coeff() && !minus_one {
                print_coefficient(f)?;
            } else {
                f.write_str("1")?;
            }
        } else {
            print_factors(&num, f)?;
        }
        f.write_str(", ")?;
        print_factors(&den, f)?;
        f.write_str(")")
    }
}

impl<T: Set> Print for Mul<T> {
    fn print(&self, options: &PrintOptions, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if options.typst {
            return self.print_typst(options, f);
        }
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
                self.print_coefficient_element(options, f)?;
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
        // Parts of the numerator and of the denominator, with whether they are sums (needing parentheses next to
        // other parts)
        let mut num: Vec<(PrettyPrinter, bool)> = vec![];
        let mut den: Vec<(PrettyPrinter, bool)> = vec![];
        // A negative coefficient is printed as a minus sign in front of the product
        let coefficient_set = self.set.get_coefficient_set();
        let negative = coefficient_set.is_strictly_negative(&self.coefficient);
        let coefficient = if negative {
            coefficient_set.neg(&self.coefficient)
        } else {
            self.coefficient.clone()
        };
        if !coefficient_set.is_one(&coefficient) {
            let print_coefficient = |coefficient: &<T::ProductCoefficientSet as Set>::Element| {
                let mut printed = coefficient_set.pretty_print(coefficient, options);
                if coefficient_set.is_sum(coefficient) {
                    printed.paren();
                }
                (printed, false)
            };
            if self.is_approximate() {
                let mut printed = coefficient_set.pretty_print_approximate(&coefficient, options);
                if coefficient_set.is_sum(&coefficient) {
                    printed.paren();
                }
                num.push((printed, false));
            } else {
                // The denominator of the coefficient goes under the fraction bar
                let (coefficient_num, coefficient_den) = coefficient_set.as_fraction(&coefficient);
                if !coefficient_set.is_one(&coefficient_num) {
                    num.push(print_coefficient(&coefficient_num));
                }
                if !coefficient_set.is_one(&coefficient_den) {
                    den.push(print_coefficient(&coefficient_den));
                }
            }
        }
        for factor in &self.factors {
            match factor {
                Term::Pow(pow) if pow.exponant.is_strictly_negative() => {
                    let mut factor = pow.clone();
                    **factor.exponant = -&**factor.exponant;
                    let factor = Term::Pow(factor).normalize();
                    den.push((
                        PrettyPrint::pretty_print(&factor, options),
                        matches!(factor, Term::Add(_)),
                    ));
                }
                _ => num.push((
                    PrettyPrint::pretty_print(factor, options),
                    matches!(factor, Term::Add(_)),
                )),
            }
        }

        let is_fraction = !den.is_empty();
        let join = |parts: Vec<(PrettyPrinter, bool)>, paren_single_sum: bool| {
            let paren_sums = parts.len() > 1 || paren_single_sum;
            let mut res: Option<PrettyPrinter> = None;
            for (mut part, is_sum) in parts {
                if is_sum && paren_sums {
                    part.paren();
                }
                if let Some(res) = &mut res {
                    res.concat("⋅", false, &part);
                } else {
                    res = Some(part);
                }
            }
            res
        };
        // `-(x + 1)` needs parentheses, `x + 1` alone over a fraction bar doesn't
        let mut res = join(num, negative && !is_fraction).unwrap_or_else(f);
        if let Some(den) = join(den, false) {
            res.vertical_concat("─", &den);
        }
        if negative {
            let mut minus = PrettyPrinter::from("-".to_string());
            minus.concat("", false, &res);
            res = minus;
        }
        res
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
