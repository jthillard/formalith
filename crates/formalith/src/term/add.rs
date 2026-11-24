//! Sum expression.

use std::fmt::Display;

use crate::{
    context::Context,
    field::{Group, Set},
    printer::{PrettyPrint, PrettyPrinter, Print, PrintOptions},
};

use super::{Flags, Term, Value};

/// A sum of expressions.
#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(not(feature = "concise-debug"), derive(Debug))]
pub struct Add<T: Set> {
    flags: u8,
    pub(crate) terms: Vec<Term<T>>,
    pub(crate) set: T,
}

#[cfg(feature = "concise-debug")]
#[allow(clippy::missing_fields_in_debug)]
impl<T: Set + std::fmt::Debug> std::fmt::Debug for Add<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Add")
            .field("terms", &self.terms)
            .field("set", &self.set)
            .finish()
    }
}

impl<T: Set> Flags for Add<T> {
    fn get_flags(&self) -> u8 {
        self.flags
    }
    fn get_flags_mut(&mut self) -> &mut u8 {
        &mut self.flags
    }
}

impl<T: Set> Add<T> {
    /// Create a sum expression from its terms.
    pub const fn new(terms: Vec<Term<T>>, set: T) -> Self {
        Self {
            flags: 0,
            terms,
            set,
        }
    }
    /// Create a new empty sum, with an inner vec with a defined capacity.
    pub fn with_capacity(capacity: usize, set: T) -> Self {
        Self::new(Vec::with_capacity(capacity), set)
    }
    /// Returns true if the addition is empty.
    pub const fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }
    /// Get the number of terms in the sum.
    pub const fn len(&self) -> usize {
        self.terms.len()
    }
    /// Add a term at the end of the sum, without normalizing it
    pub fn push(&mut self, value: Term<T>) {
        self.set_normalized(false);
        self.terms.push(value);
    }
    /// Return an iterator over the sum terms
    pub fn iter(&self) -> std::slice::Iter<'_, Term<T>> {
        self.terms.iter()
    }
}

impl<T: Set> IntoIterator for Add<T> {
    type Item = Term<T>;

    type IntoIter = std::vec::IntoIter<Term<T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.terms.into_iter()
    }
}

impl<'a, T: Set> IntoIterator for &'a Add<T> {
    type Item = &'a Term<T>;

    type IntoIter = std::slice::Iter<'a, Term<T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.terms.iter()
    }
}

/// Whether the element `a` of `set` prints as a minus sign followed by its opposite in a sum: negative elements,
/// and elements of unordered sets printed with a single leading sign, like `{$-i$}` (`{$x - i$}`, not
/// `{$x + -i$}`).
fn prints_negative<S: Group>(set: S, a: &S::Element, options: PrintOptions) -> bool {
    struct Printed<'a, S: Set>(S, &'a S::Element, &'a PrintOptions);
    impl<S: Set> Display for Printed<'_, S> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            self.0.print(self.1, self.2, f)
        }
    }
    set.is_strictly_negative(a)
        || Printed(set, a, &options)
            .to_string()
            .strip_prefix('-')
            .is_some_and(|rest| !rest.contains(['+', '-']))
}

impl<T: Set> Add<T> {
    /// The terms in printing order: remainders `{$o(u)$}` last, like in `{$1 + x + o(x)$}`.
    fn print_order(&self) -> impl Iterator<Item = &Term<T>> {
        let is_little_o = |term: &&Term<T>| matches!(term, Term::Fun(fun) if fun.get_ident() == Context::LITTLE_O);
        let (little_o, others): (Vec<_>, Vec<_>) = self.terms.iter().partition(is_little_o);
        others.into_iter().chain(little_o)
    }

    fn print_default<
        F: FnMut(&Term<T>, &mut std::fmt::Formatter<'_>) -> Result<bool, std::fmt::Error>,
    >(
        &self,
        mut special_cases: F,
        options: crate::printer::PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        for (i, term) in self.print_order().enumerate() {
            if !special_cases(term, f)? {
                match term {
                    Term::Mul(mul)
                        if prints_negative(
                            mul.set.get_coefficient_set(),
                            &mul.get_coeff(),
                            options,
                        ) && i != 0 =>
                    {
                        let mut mul = mul.clone();
                        let coeff = &mut mul.coefficient;
                        mul.set.get_coefficient_set().neg_assign(coeff);
                        Self::operator("-", &options, f)?;
                        Print::print(&mul, &options, f)?;
                    }
                    _ => {
                        if i != 0 {
                            Self::operator("+", &options, f)?;
                        }
                        Print::print(term, &options, f)?;
                    }
                }
            }
        }
        Ok(())
    }
}

impl<T: Set> Print for Add<T> {
    default fn print(
        &self,
        options: &crate::printer::PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        self.print_default(|_, _| Ok(false), *options, f)
    }
}

impl<T: Group> Print for Add<T> {
    fn print(
        &self,
        options: &crate::printer::PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        self.print_default(
            |term, f| {
                Ok(
                    if let Term::Value(Value { value, set, .. }) = term
                        && prints_negative(*set, value, *options)
                    {
                        Self::operator("-", options, f)?;
                        Print::print(&Value::new(set.neg(value), *set), options, f)?;
                        true
                    } else {
                        false
                    },
                )
            },
            *options,
            f,
        )
    }
}

impl<T: Set> Add<T> {
    fn pretty_print_default<F: FnMut(&Term<T>, &mut Option<PrettyPrinter>) -> bool>(
        &self,
        mut special_cases: F,
        options: PrintOptions,
    ) -> crate::printer::PrettyPrinter {
        let mut res: Option<PrettyPrinter> = None;
        for term in self.print_order() {
            if !special_cases(term, &mut res) {
                match term {
                    Term::Mul(mul)
                        if prints_negative(
                            mul.set.get_coefficient_set(),
                            &mul.get_coeff(),
                            options,
                        ) && res.is_some() =>
                    {
                        let mut mul = mul.clone();
                        let coeff = &mut mul.coefficient;
                        mul.set.get_coefficient_set().neg_assign(coeff);
                        let elem = PrettyPrint::pretty_print(&mul, &options);
                        res.as_mut().unwrap().concat("-", true, &elem);
                    }
                    _ => {
                        let elem = PrettyPrint::pretty_print(term, &options);
                        if let Some(res) = &mut res {
                            res.concat("+", true, &elem);
                        } else {
                            res = Some(elem);
                        }
                    }
                }
            }
        }
        res.unwrap()
    }
}

impl<T: Set> PrettyPrint for Add<T> {
    default fn pretty_print(&self, options: &PrintOptions) -> crate::printer::PrettyPrinter {
        self.pretty_print_default(|_, _| false, *options)
    }
}

impl<T: Group> PrettyPrint for Add<T> {
    fn pretty_print(&self, options: &PrintOptions) -> crate::printer::PrettyPrinter {
        self.pretty_print_default(
            |term, res| {
                if let Term::Value(Value { value, set, .. }) = term
                    && let Some(res) = res
                    && prints_negative(*set, value, *options)
                {
                    let elem =
                        PrettyPrint::pretty_print(&Value::new(set.neg(value), *set), options);
                    res.concat("-", true, &elem);
                    true
                } else {
                    false
                }
            },
            *options,
        )
    }
}

impl<T: Set> Display for Add<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        PrettyPrint::fmt(self, &PrintOptions::default(), f)
    }
}
