//! Linear systems, solved by Gaussian elimination.

use std::collections::BTreeMap;

use crate::{
    context::Symbol,
    field::Ring,
    matrix::Matrix,
    term::{Mul, Normalize, SymbolTerm, Term},
};

use super::{Solution, SolveError, plain};

/// Solve the linear system `expression = 0` for each expanded expression, in `unknowns`.
///
/// When every coefficient is a value, the elimination is done in `set`, so pivots must be invertible. Otherwise it
/// is done with expressions as coefficients, assuming that symbolic pivots, like `a` in `a*x = 1`, are not zero.
///
/// # Errors
/// Returns an error if an expression is not linear in the unknowns, or if a pivot is not invertible.
pub(super) fn solve<T: Ring>(
    expressions: &[Term<T>],
    unknowns: &[Symbol],
    set: T,
) -> Result<Solution<T>, SolveError> {
    let forms = expressions
        .iter()
        .map(|expression| linear_form(expression, unknowns, set))
        .collect::<Result<Vec<_>, _>>()?;

    // The augmented matrix `(A | B)` of `A X = B`
    let size = (forms.len(), unknowns.len() + 1);
    let mut data = Vec::with_capacity(size.0 * size.1);
    for (mut coefficients, constant) in forms {
        for unknown in unknowns {
            data.push(coefficients.remove(unknown).unwrap_or(Term::zero(set)));
        }
        data.push(-constant);
    }

    let values = data
        .iter()
        .map(|term| match term {
            Term::Value(value) => Some(value.value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>();
    if let Some(values) = values {
        return solve_matrix(
            Matrix::new(size, values, set),
            set,
            unknowns,
            set,
            |value| Term::constant(value.clone(), set),
        );
    }
    let term_set = set.get_term_set();
    let solution = solve_matrix(
        Matrix::new(size, data, term_set),
        term_set,
        unknowns,
        set,
        Clone::clone,
    )?;
    // The elimination nests fractions, like `(f - e*c/a) / (d - b*c/a)`
    Ok(match solution {
        Solution::Assignments(assignments) => Solution::Assignments(
            assignments
                .into_iter()
                .map(|(unknown, value)| (unknown, value.simplify()))
                .collect(),
        ),
        solution => solution,
    })
}

/// Solve the system of augmented matrix `matrix`, with coefficients in `coefficient_set`, converted to
/// expressions with `to_term`.
fn solve_matrix<T: Ring, K: Ring>(
    mut matrix: Matrix<K>,
    coefficient_set: K,
    unknowns: &[Symbol],
    set: T,
    to_term: impl Fn(&K::Element) -> Term<T>,
) -> Result<Solution<T>, SolveError> {
    let count = unknowns.len();
    matrix
        .row_reduce_left(count)
        .map_err(|_| SolveError::NotInvertible)?;

    // Pivots, as (row, column)
    let mut pivots = vec![];
    for row in 0..matrix.height() {
        match (0..count).find(|&column| !coefficient_set.is_zero(&matrix[(row, column)])) {
            Some(column) => pivots.push((row, column)),
            // `0 = b` with `b` non-zero
            None if !coefficient_set.is_zero(&matrix[(row, count)]) => {
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
            let mut value = to_term(&matrix[(row, count)]);
            for &free in &free {
                let coefficient = &matrix[(row, free)];
                if !coefficient_set.is_zero(coefficient) {
                    value = value
                        - to_term(coefficient) * Term::Symbol(SymbolTerm::new(unknowns[free], set));
                }
            }
            (unknowns[column], value)
        })
        .collect();
    Ok(Solution::Assignments(assignments))
}

/// Split an expanded expression into its coefficients `a_i` and its constant `b`, so that it is
/// `sum(a_i x_i) + b` with `x_i` the unknowns. Coefficients and the constant don't contain unknowns.
fn linear_form<T: Ring>(
    expression: &Term<T>,
    unknowns: &[Symbol],
    set: T,
) -> Result<(BTreeMap<Symbol, Term<T>>, Term<T>), SolveError> {
    let has_unknown = |term: &Term<T>| {
        term.symbols()
            .iter()
            .any(|symbol| unknowns.contains(symbol))
    };
    let non_linear = |term: &Term<T>| SolveError::NonLinear(plain(term));
    let terms = match expression {
        Term::Add(add) => add.terms.as_slice(),
        term => std::slice::from_ref(term),
    };
    let mut coefficients = BTreeMap::new();
    let mut constant = Term::zero(set);
    for term in terms {
        if !has_unknown(term) {
            constant += term;
            continue;
        }
        let (symbol, coefficient) = match term {
            Term::Symbol(symbol) => (symbol.symbol, Term::one(set)),
            // `c * f_1 * ... * x * ... * f_n`, where only `x` contains an unknown
            Term::Mul(mul) => {
                let mut factors = mul.factors.iter().filter(|factor| has_unknown(factor));
                let (Some(Term::Symbol(symbol)), None) = (factors.next(), factors.next()) else {
                    return Err(non_linear(term));
                };
                let others = mul
                    .factors
                    .iter()
                    .filter(|factor| !has_unknown(factor))
                    .cloned()
                    .collect();
                let coefficient = Term::Mul(Mul::new(mul.coefficient.clone(), others, set));
                (symbol.symbol, coefficient.normalize())
            }
            _ => return Err(non_linear(term)),
        };
        *coefficients.entry(symbol).or_insert(Term::zero(set)) += coefficient;
    }
    Ok((coefficients, constant))
}
