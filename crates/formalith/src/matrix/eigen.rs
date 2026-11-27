//! Eigenvalues and eigenvectors of real or complex matrices, from the roots of the characteristic polynomial.

use malachite::rational::Rational;

use crate::{
    context::Symbol,
    field::{Derivable, Group, real::R},
    solve::{Equation, Solution, Solve, polynomial::polynomial_form},
    term::{Expand, Term, TermSet},
};

/// The sets whose matrices have eigenvalues, `{$RR$}` and `{$CC$}`: their terms can be differentiated and
/// polynomial equations solved.
pub trait EigenSet: Derivable<ExponantSet = Self, ProductCoefficientSet = Self> {}

impl<T: Derivable<ExponantSet = T, ProductCoefficientSet = T>> EigenSet for T {}

use super::Matrix;

/// Whether `term` is zero, once written as a fraction with an expanded numerator, like `{$4 - r - 6/(1 - r)$}`
/// for a root `r` of `{$r^2 - 5 r - 2$}`.
fn vanishes<T: EigenSet>(term: &Term<T>) -> bool {
    term.is_zero() || term.as_fraction(true).0.expand().is_zero()
}

/// A basis of the kernel of `matrix` as in [`Matrix::kernel`], with entries simplified at each step of the
/// elimination and zero tests done by [`vanishes`], since entries of a matrix shifted by a radical eigenvalue
/// often don't vanish structurally.
fn kernel<T: EigenSet>(mut matrix: Matrix<TermSet<T>>) -> Matrix<TermSet<T>> {
    let set = *matrix.set.get_set();
    let (height, width) = (matrix.height(), matrix.width());
    let mut pivots = vec![];
    for column in 0..width {
        let row = pivots.len();
        let Some(pivot) = (row..height).find(|&i| !vanishes(&matrix[(i, column)])) else {
            for i in row..height {
                matrix[(i, column)] = Term::zero(set);
            }
            continue;
        };
        matrix.swap_rows(row, pivot);
        let inverse = matrix[(row, column)].inv();
        matrix.scale_row(row, &inverse);
        for i in (0..height).filter(|&i| i != row) {
            let factor = -matrix[(i, column)].clone();
            matrix.row_add(i, row, &factor);
        }
        for entry in &mut matrix.data {
            *entry = if vanishes(entry) {
                Term::zero(set)
            } else {
                entry.simplify()
            };
        }
        pivots.push(column);
        if pivots.len() == height {
            break;
        }
    }
    let free: Vec<usize> = (0..width)
        .filter(|column| !pivots.contains(column))
        .collect();
    if free.is_empty() {
        return Matrix::zero((width, 1), matrix.set);
    }
    let mut basis = Matrix::zero((width, free.len()), matrix.set);
    for (k, &column) in free.iter().enumerate() {
        basis[(column, k)] = Term::one(set);
        for (row, &pivot) in pivots.iter().enumerate() {
            basis[(pivot, k)] = -matrix[(row, column)].clone();
        }
    }
    basis
}

/// The real roots of the expanded polynomial `p` in `x` found by [`Solve::solve_for`], with their
/// multiplicities, in the order of its solutions. Returns `None` if they can't be computed.
pub fn real_roots(p: &Term<R<Rational>>, x: Symbol) -> Option<Vec<(Term<R<Rational>>, usize)>> {
    roots(p, x)
}

/// The roots of the expanded polynomial `p` in `x` in its set found by [`Solve::solve_for`], with their
/// multiplicities, in the order of its solutions. Returns `None` if they can't be computed.
pub fn roots<T: EigenSet>(p: &Term<T>, x: Symbol) -> Option<Vec<(Term<T>, usize)>> {
    let roots = match p
        .get_set()
        .solve_for(&[Equation::new(p.clone(), Term::zero(p.get_set()))], &[x])
        .ok()?
    {
        Solution::Assignments(assignments) => vec![assignments],
        Solution::Alternatives(branches) => branches,
        Solution::NoSolution => vec![],
    };
    // As many distinct roots as the degree: they are all simple, without the zero tests below, slow with radicals
    let degree = polynomial_form(p, x).ok()?.len().saturating_sub(1);
    if roots.len() == degree {
        return roots
            .into_iter()
            .map(|assignments| match assignments.as_slice() {
                [(_, value)] => Some((value.clone(), 1)),
                _ => None,
            })
            .collect();
    }
    let mut multiplicities = vec![];
    for assignments in roots {
        let [(_, value)] = assignments.as_slice() else {
            return None;
        };
        // The multiplicity is the order of the first derivative which doesn't vanish at the root
        let mut multiplicity = 0;
        let mut derivative = p.clone();
        while derivative
            .substitute(x, value)?
            .expand()
            .simplify()
            .is_zero()
        {
            multiplicity += 1;
            derivative = derivative.derivative(x).expand();
        }
        multiplicities.push((value.clone(), multiplicity));
    }
    Some(multiplicities)
}

/// An eigenvalue of a matrix with its eigenspace.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Eigenspace<T: EigenSet> {
    /// The eigenvalue.
    pub value: Term<T>,
    /// The algebraic multiplicity of the eigenvalue, its multiplicity as a root of the characteristic polynomial.
    pub multiplicity: usize,
    /// A basis of the eigenspace, as the columns of a matrix.
    pub basis: Matrix<TermSet<T>>,
}

impl<T: EigenSet> Matrix<TermSet<T>> {
    /// The eigenvalues of the matrix with their eigenspaces, sorted like the solutions of
    /// [`Solve::solve_for`]. Returns `None` if the matrix is not square, or if the roots of its characteristic
    /// polynomial can't all be computed in the set of the entries (for instance in `{$RR$}` when some of them
    /// aren't real).
    #[must_use]
    pub fn eigenspaces(&self) -> Option<Vec<Eigenspace<T>>> {
        let x = Symbol::new("@l");
        let charpoly = self.charpoly(x).ok()?.expand();
        let multiplicities = roots(&charpoly, x)?;
        // Before computing eigenspaces, which is slow with radicals, `{$x^3 - 4 x^2 - 3 x + 37$}` having non-real roots
        let total: usize = multiplicities
            .iter()
            .map(|(_, multiplicity)| multiplicity)
            .sum();
        if total != self.height() {
            return None;
        }
        let eigenspaces = multiplicities
            .into_iter()
            .map(|(value, multiplicity)| {
                let mut shifted = self.clone();
                for i in 0..self.height() {
                    shifted[(i, i)] = self.set.sub(&self[(i, i)], &value);
                }
                Eigenspace {
                    value,
                    multiplicity,
                    basis: kernel(shifted),
                }
            })
            .collect();
        Some(eigenspaces)
    }
}
