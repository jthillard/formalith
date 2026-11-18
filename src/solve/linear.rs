//! Linear systems, solved by Gaussian elimination.

use std::collections::BTreeMap;

use crate::{
    context::{Context, Symbol},
    field::{Ring, Set, TryElementFrom},
    matrix::Matrix,
    printer::{Print, PrintOptions},
    term::{SymbolTerm, Term},
};

use super::{Solution, SolveError};

/// A linear system `A X = B`, stored as the augmented matrix `(A | B)`.
pub(super) struct LinearSystem<T: Ring> {
    /// The unknowns, in the order of the columns.
    unknowns: Vec<Symbol>,
    matrix: Matrix<T>,
    set: T,
}

impl<T: Ring + TryElementFrom<<T as Set>::ProductCoefficientSet>> LinearSystem<T> {
    /// Build the system `expression = 0` for each expanded expression.
    ///
    /// # Errors
    /// Returns an error if an expression is not linear.
    pub(super) fn new(expressions: &[Term<T>], set: T) -> Result<Self, SolveError> {
        let forms = expressions
            .iter()
            .map(|expression| linear_form(expression, set))
            .collect::<Result<Vec<_>, _>>()?;
        let mut unknowns: Vec<Symbol> = forms
            .iter()
            .flat_map(|(coefficients, _)| coefficients.keys().copied())
            .collect();
        // Sort by name, so that the solution doesn't depend on the order symbols were created in
        unknowns.sort_by(|a, b| {
            Context::get_symbol_data(a)
                .name
                .cmp(&Context::get_symbol_data(b).name)
        });
        unknowns.dedup();

        let width = unknowns.len() + 1;
        let mut data = Vec::with_capacity(forms.len() * width);
        for (coefficients, constant) in &forms {
            for unknown in &unknowns {
                data.push(coefficients.get(unknown).cloned().unwrap_or(set.zero()));
            }
            data.push(set.neg(constant));
        }
        Ok(Self {
            unknowns,
            matrix: Matrix::new((forms.len(), width), data, set),
            set,
        })
    }

    /// Solve the system.
    ///
    /// # Errors
    /// Returns an error if a pivot is not invertible.
    pub(super) fn solve(mut self) -> Result<Solution<T>, SolveError> {
        let count = self.unknowns.len();
        self.matrix
            .row_reduce_left(count)
            .map_err(|_| SolveError::NotInvertible)?;

        // Pivots, as (row, column)
        let mut pivots = vec![];
        for row in 0..self.matrix.height() {
            match (0..count).find(|&column| !self.set.is_zero(&self.matrix[(row, column)])) {
                Some(column) => pivots.push((row, column)),
                // `0 = b` with `b` non-zero
                None if !self.set.is_zero(&self.matrix[(row, count)]) => {
                    return Ok(Solution::NoSolution);
                }
                None => {}
            }
        }
        let free: Vec<usize> = (0..count)
            .filter(|column| pivots.iter().all(|(_, pivot)| pivot != column))
            .collect();

        // Pivots are one, so `x_pivot = b - sum(a_free * x_free)`
        let assignments = pivots
            .iter()
            .map(|&(row, column)| {
                let mut value = Term::constant(self.matrix[(row, count)].clone(), self.set);
                for &free in &free {
                    let coefficient = &self.matrix[(row, free)];
                    if !self.set.is_zero(coefficient) {
                        value = value
                            - Term::constant(coefficient.clone(), self.set)
                                * Term::Symbol(SymbolTerm::new(self.unknowns[free], self.set));
                    }
                }
                (self.unknowns[column], value)
            })
            .collect();
        Ok(Solution::Assignments(assignments))
    }
}

/// Split an expanded expression into its coefficients `a_i` and its constant `b`, so that it is `sum(a_i x_i) + b`.
fn linear_form<T: Ring + TryElementFrom<<T as Set>::ProductCoefficientSet>>(
    expression: &Term<T>,
    set: T,
) -> Result<(BTreeMap<Symbol, T::Element>, T::Element), SolveError> {
    let non_linear = |term: &Term<T>| {
        let options = PrintOptions {
            colors: false,
            typst: false,
            pretty_print: false,
        };
        SolveError::NonLinear(term.with_options(options).to_string())
    };
    let terms = match expression {
        Term::Add(add) => add.terms.as_slice(),
        term => std::slice::from_ref(term),
    };
    let mut coefficients = BTreeMap::new();
    let mut constant = set.zero();
    for term in terms {
        let (symbol, coefficient) = match term {
            Term::Value(value) => {
                set.add_assign(&mut constant, &value.value);
                continue;
            }
            Term::Symbol(symbol) => (symbol.symbol, set.one()),
            Term::Mul(mul) => match mul.factors.as_slice() {
                [Term::Symbol(symbol)] => (
                    symbol.symbol,
                    <T as TryElementFrom<<T as Set>::ProductCoefficientSet>>::try_from_element(
                        mul.coefficient.clone(),
                    )
                    .map_err(|_| non_linear(term))?,
                ),
                _ => return Err(non_linear(term)),
            },
            Term::Pow(_) | Term::Fun(_) | Term::Add(_) => return Err(non_linear(term)),
        };
        let entry = coefficients.entry(symbol).or_insert(set.zero());
        set.add_assign(entry, &coefficient);
    }
    Ok((coefficients, constant))
}
