//! Linear systems over `{$ZZ$}` and `{$ZZ\/n ZZ$}` whose pivots aren't invertible, like `2 x = 4`, solved with
//! the Hermite and Smith normal forms.

use std::collections::BTreeSet;

use malachite::{
    Integer,
    base::num::arithmetic::traits::{DivisibleBy, Mod},
};

use crate::{
    context::Symbol,
    field::{EuclideanRing, Ring, integer::Z, modular::Zn},
    matrix::Matrix,
    term::{SymbolTerm, Term},
};

use super::{Assignments, Solution, SolveError, linear::assignments};

/// Maximum number of solutions listed for a system over `{$ZZ\/n ZZ$}`, like `x = 2 \ x = 5` for `2 x = 4` in
/// `{$ZZ\/6 ZZ$}`.
const MAX_BRANCHES: usize = 256;

/// Sets whose linear systems can be solved when a pivot isn't invertible. Implemented for every ring, failing
/// with [`SolveError::NotInvertible`] except for `{$ZZ$}` and `{$ZZ\/n ZZ$}`.
pub(super) trait IntegerSystem: Ring {
    /// Solve the system of augmented matrix `matrix` in `unknowns`. New parameters `t_1, t_2, ...` are named
    /// without the names of `symbols`.
    fn solve_lattice(
        &self,
        matrix: &Matrix<Self>,
        unknowns: &[Symbol],
        symbols: &BTreeSet<Symbol>,
    ) -> Result<Solution<Self>, SolveError>;
}

impl<T: Ring> IntegerSystem for T {
    default fn solve_lattice(
        &self,
        _: &Matrix<Self>,
        _: &[Symbol],
        _: &BTreeSet<Symbol>,
    ) -> Result<Solution<Self>, SolveError> {
        Err(SolveError::NotInvertible)
    }
}

impl IntegerSystem for Z<Integer> {
    /// When every pivot of the Hermite normal form divides its row, unknowns without pivot stay free, like
    /// `x = 3 - 2 y` for `2 x + 4 y = 6`. Otherwise new parameters are needed, like `x = 3 t_1 - 1, y = 1 - 2 t_1`
    /// for `2 x + 3 y = 1`, see [`smith`].
    fn solve_lattice(
        &self,
        matrix: &Matrix<Self>,
        unknowns: &[Symbol],
        symbols: &BTreeSet<Symbol>,
    ) -> Result<Solution<Self>, SolveError> {
        let count = unknowns.len();
        let (_, mut hermite, rank) = matrix.hermite_decomposition_left(count);
        let pivots: Vec<usize> = (0..rank)
            .map(|row| {
                (0..count)
                    .find(|&column| hermite[(row, column)] != 0)
                    .expect("Rows of the rank have a pivot")
            })
            .collect();
        let divides = pivots.iter().enumerate().all(|(row, &column)| {
            let pivot = &hermite[(row, column)];
            (column..=count).all(|j| (&hermite[(row, j)]).divisible_by(pivot))
        });
        if !divides {
            return smith(matrix, unknowns, symbols, None);
        }
        for (row, &column) in pivots.iter().enumerate() {
            let pivot = hermite[(row, column)].clone();
            for j in column..=count {
                hermite[(row, j)] /= &pivot;
            }
        }
        // Pivots are one, eliminate the entries above them
        for (row, &column) in pivots.iter().enumerate().rev() {
            for above in 0..row {
                let factor = -hermite[(above, column)].clone();
                hermite.row_add(above, row, &factor);
            }
        }
        assignments(&hermite, Z, unknowns, Z, |value| {
            Term::constant(value.clone(), Z)
        })
    }
}

impl IntegerSystem for Zn {
    /// Solved over `{$ZZ$}` modulo `n` by [`smith`], listing the finitely many solutions coming from zero divisors.
    fn solve_lattice(
        &self,
        matrix: &Matrix<Self>,
        unknowns: &[Symbol],
        symbols: &BTreeSet<Symbol>,
    ) -> Result<Solution<Self>, SolveError> {
        let lifted = Matrix::new(
            (matrix.height(), matrix.width()),
            matrix.data.iter().copied().map(Integer::from).collect(),
            Z,
        );
        let solution = smith(&lifted, unknowns, symbols, Some(self.modulus()))?;
        let reduce = |assignments: Assignments<Z<Integer>>| -> Assignments<Self> {
            assignments
                .into_iter()
                .map(|(unknown, value)| (unknown, self.reduce_term(&value)))
                .collect()
        };
        Ok(match solution {
            Solution::NoSolution => Solution::NoSolution,
            Solution::Assignments(assignments) => {
                Solution::from_branches(vec![reduce(assignments)])
            }
            Solution::Alternatives(branches) => {
                Solution::from_branches(branches.into_iter().map(reduce).collect())
            }
        })
    }
}

impl Zn {
    /// The expression of `{$ZZ$}` `term`, a sum of products of integers and symbols, reduced modulo `n`.
    fn reduce_term(self, term: &Term<Z<Integer>>) -> Term<Self> {
        match term {
            Term::Value(value) => Term::constant(self.reduce(&value.value), self),
            Term::Symbol(symbol) => Term::Symbol(SymbolTerm::new(symbol.symbol, self)),
            Term::Add(add) => add
                .terms
                .iter()
                .fold(Term::zero(self), |sum, term| sum + self.reduce_term(term)),
            Term::Mul(mul) => mul.factors.iter().fold(
                Term::constant(self.reduce(&mul.coefficient), self),
                |product, factor| product * self.reduce_term(factor),
            ),
            Term::Pow(_) | Term::Fun(_) => unreachable!("Solutions are linear in the parameters"),
        }
    }
}

/// Solve the system of augmented integer matrix `(A | b)`, over `{$ZZ$}` or modulo `modulus`, with the Smith
/// normal form `{$U A V = D$}`: `{$A x = b$}` is `{$D y = U b$}` with `{$x = V y$}`. Each `{$d_i y_i = c_i$}` has
/// one solution in `{$ZZ$}` when `d_i` divides `c_i`. Modulo `n`, it has `{$g = gcd(d_i, n)$}` of them when `g`
/// divides `c_i`, giving one branch each. `y_i` is a new parameter when `{$d_i = 0$}`.
fn smith(
    matrix: &Matrix<Z<Integer>>,
    unknowns: &[Symbol],
    symbols: &BTreeSet<Symbol>,
    modulus: Option<u64>,
) -> Result<Solution<Z<Integer>>, SolveError> {
    let count = unknowns.len();
    let coefficients = matrix.submatrix(0..matrix.height(), 0..count);
    let (left, diagonal, right) = coefficients.smith_decomposition();
    let constants = &left * &matrix.submatrix(0..matrix.height(), count..count + 1);
    let modulus = modulus.map(Integer::from);
    let reduce = |value: Integer| match &modulus {
        Some(n) => value.mod_op(n),
        None => value,
    };
    let mut parameters = (1..)
        .map(|i| Symbol::new(format!("t_{i}")))
        .filter(|t| !symbols.contains(t) && !unknowns.contains(t));
    // The possible values of each `y_i`, as `(values, parameter)`: `y_i = value + parameter`
    let mut choices: Vec<(Vec<Integer>, Option<Symbol>)> = vec![];
    for i in 0..matrix.height().max(count) {
        let d = if i < count && i < matrix.height() {
            diagonal[(i, i)].clone()
        } else {
            Integer::from(0)
        };
        let c = if i < matrix.height() {
            reduce(constants[(i, 0)].clone())
        } else {
            Integer::from(0)
        };
        let g = match &modulus {
            Some(n) => Z.gcd(&d, n),
            None => d.clone(),
        };
        if g == 0 {
            // `0 y_i = c_i` over `{$ZZ$}`
            if c != 0 {
                return Ok(Solution::NoSolution);
            }
            if i < count {
                choices.push((vec![Integer::from(0)], parameters.next()));
            }
            continue;
        }
        if !(&c).divisible_by(&g) {
            return Ok(Solution::NoSolution);
        }
        if i >= count {
            continue;
        }
        let values = match &modulus {
            None => vec![c / &d],
            Some(n) if d == 0 => {
                // `0 y_i = 0` modulo `n`, `y_i` is any residue
                debug_assert_eq!(g, *n);
                choices.push((vec![Integer::from(0)], parameters.next()));
                continue;
            }
            Some(n) => {
                // `y = (c/g) (d/g)^-1` modulo `n/g`, then every lift modulo `n`
                let step = n / &g;
                let y = if step == 1 {
                    Integer::from(0)
                } else {
                    let ring = Zn::new(u64::try_from(&step).expect("The modulus fits in u64"));
                    let inverse = ring
                        .try_inv(&ring.reduce(&(&d / &g)))
                        .expect("d/g and n/g are coprime");
                    (&c / &g * Integer::from(inverse)).mod_op(&step)
                };
                (0..u64::try_from(&g).expect("The gcd fits in u64"))
                    .map(|k| &y + Integer::from(k) * &step)
                    .collect()
            }
        };
        choices.push((values, None));
    }
    let branches: usize = choices
        .iter()
        .try_fold(1usize, |product, (values, _)| {
            product.checked_mul(values.len())
        })
        .filter(|&branches| branches <= MAX_BRANCHES)
        .ok_or(SolveError::Unsupported)?;
    let mut solutions = Vec::with_capacity(branches);
    for mut index in 0..branches {
        // `y` for this branch, with mixed radix digits of `index` choosing the values
        let y: Vec<Term<Z<Integer>>> = choices
            .iter()
            .map(|(values, parameter)| {
                let value = values[index % values.len()].clone();
                index /= values.len();
                let value = Term::constant(value, Z);
                match parameter {
                    Some(t) => value + Term::Symbol(SymbolTerm::new(*t, Z)),
                    None => value,
                }
            })
            .collect();
        solutions.push(
            unknowns
                .iter()
                .enumerate()
                .map(|(k, unknown)| {
                    let x = y.iter().enumerate().fold(Term::zero(Z), |x, (j, y)| {
                        x + Term::constant(reduce(right[(k, j)].clone()), Z) * y.clone()
                    });
                    (*unknown, x)
                })
                .collect(),
        );
    }
    Ok(Solution::from_branches(solutions))
}
