//! Linear algebra on matrices: transpose, trace, rank, kernel and characteristic polynomial.

use crate::{
    context::Symbol,
    field::{Group, Ring, Set},
    term::{SymbolTerm, Term, TermSet},
};

use super::{Matrix, MatrixError, MatrixResult};

impl<T: Set> Matrix<T> {
    /// The transpose of the matrix.
    #[must_use]
    pub fn transpose(&self) -> Self {
        let data = (0..self.width())
            .flat_map(|j| (0..self.height()).map(move |i| (i, j)))
            .map(|index| self[index].clone())
            .collect();
        Self::new((self.width(), self.height()), data, self.set)
    }

    /// Swap two columns in the matrix.
    pub fn swap_columns(&mut self, column1: usize, column2: usize) {
        for row in 0..self.height() {
            let width = self.width();
            self.data.swap(row * width + column1, row * width + column2);
        }
    }

    /// The submatrix made of the rows `rows` and the columns `columns`.
    #[must_use]
    pub fn submatrix(&self, rows: std::ops::Range<usize>, columns: std::ops::Range<usize>) -> Self {
        let size = (rows.len(), columns.len());
        let data = rows
            .flat_map(|i| columns.clone().map(move |j| (i, j)))
            .map(|index| self[index].clone())
            .collect();
        Self::new(size, data, self.set)
    }
}

impl<T: Group> Matrix<T> {
    /// The matrix made of the columns of `self` followed by those of `other`, which must have the same height.
    #[must_use]
    pub fn concat_columns(&self, other: &Self) -> Self {
        debug_assert_eq!(self.height(), other.height());
        let data = (0..self.height())
            .flat_map(|i| {
                (0..self.width())
                    .map(move |j| self[(i, j)].clone())
                    .chain((0..other.width()).map(move |j| other[(i, j)].clone()))
            })
            .collect();
        Self::new(
            (self.height(), self.width() + other.width()),
            data,
            self.set,
        )
    }
}

impl<T: Ring> Matrix<T> {
    /// The identity matrix of size `n`.
    #[must_use]
    pub fn identity(n: usize, set: T) -> Self {
        let mut identity = Self::zero((n, n), set);
        for i in 0..n {
            identity[(i, i)] = set.one();
        }
        identity
    }

    /// Add a column multiplied by a factor to another.
    pub fn column_add(&mut self, target_column: usize, source_column: usize, factor: &T::Element) {
        for row in 0..self.height() {
            let term = self.set.mul(&self[(row, source_column)], factor);
            self[(row, target_column)] = self.set.add(&self[(row, target_column)], &term);
        }
    }

    /// The trace of the matrix, the sum of its diagonal.
    ///
    /// # Errors
    /// Returns an error if the matrix is not square.
    pub fn trace(&self) -> MatrixResult<T::Element> {
        if self.width() != self.height() {
            return Err(MatrixError::NotSquare);
        }
        Ok((0..self.height()).fold(self.set.zero(), |trace, i| {
            self.set.add(&trace, &self[(i, i)])
        }))
    }

    /// The rank of the matrix.
    ///
    /// # Errors
    /// The method will fail if a pivot is not invertible.
    pub fn rank(&self) -> MatrixResult<usize> {
        self.clone().partial_row_reduce()
    }

    /// A basis of the kernel of the matrix, as the columns of the result. The kernel `{$\{0\}$}` is given as a
    /// zero column, since a matrix can't be empty.
    ///
    /// # Errors
    /// The method will fail if a pivot is not invertible.
    pub fn kernel(&self) -> MatrixResult<Self> {
        let mut reduced = self.clone();
        reduced.row_reduce()?;
        // Pivots are one, so `x_pivot = -sum(a_free * x_free)`
        let pivots: Vec<(usize, usize)> = (0..reduced.height())
            .filter_map(|row| {
                (0..reduced.width())
                    .find(|&column| !self.set.is_zero(&reduced[(row, column)]))
                    .map(|column| (row, column))
            })
            .collect();
        let free: Vec<usize> = (0..self.width())
            .filter(|column| pivots.iter().all(|(_, pivot)| pivot != column))
            .collect();
        if free.is_empty() {
            return Ok(Self::zero((self.width(), 1), self.set));
        }
        let mut basis = Self::zero((self.width(), free.len()), self.set);
        for (k, &column) in free.iter().enumerate() {
            basis[(column, k)] = self.set.one();
            for &(row, pivot) in &pivots {
                basis[(pivot, k)] = self.set.neg(&reduced[(row, column)]);
            }
        }
        Ok(basis)
    }

    /// The coefficients of the characteristic polynomial `{$det(x I - A)$}`, from the leading one (which is
    /// one) to the constant one.
    ///
    /// It uses the Samuelson-Berkowitz algorithm, without divisions, so it works in any commutative ring.
    ///
    /// # Errors
    /// Returns an error if the matrix is not square.
    pub fn charpoly_coefficients(&self) -> MatrixResult<Vec<T::Element>> {
        if self.width() != self.height() {
            return Err(MatrixError::NotSquare);
        }
        let n = self.height();
        let set = self.set;
        // Characteristic polynomial of the bottom right submatrix of size `n - k`, starting with the empty one
        let mut coefficients = vec![set.one()];
        for k in (0..n).rev() {
            let m = n - k - 1;
            // First column of the Toeplitz matrix: `1, -a, -R C, -R A_1 C, ..., -R A_1^(m-1) C`, where
            // `[[a, R], [C, A_1]]` is the submatrix
            let mut toeplitz = vec![set.one(), set.neg(&self[(k, k)])];
            let mut vector: Vec<T::Element> = (k + 1..n).map(|i| self[(i, k)].clone()).collect();
            for _ in 0..m {
                let dot = (k + 1..n).zip(&vector).fold(set.zero(), |dot, (j, v)| {
                    set.add(&dot, &set.mul(&self[(k, j)], v))
                });
                toeplitz.push(set.neg(&dot));
                vector = (k + 1..n)
                    .map(|i| {
                        (k + 1..n).zip(&vector).fold(set.zero(), |sum, (j, v)| {
                            set.add(&sum, &set.mul(&self[(i, j)], v))
                        })
                    })
                    .collect();
            }
            coefficients = (0..m + 2)
                .map(|i| {
                    (0..=i.min(m)).fold(set.zero(), |sum, j| {
                        set.add(&sum, &set.mul(&toeplitz[i - j], &coefficients[j]))
                    })
                })
                .collect();
        }
        Ok(coefficients)
    }
}

impl<T: Ring> Matrix<TermSet<T>> {
    /// The characteristic polynomial `{$det(x I - A)$}` of the matrix, as an expression in `x`.
    ///
    /// # Errors
    /// Returns an error if the matrix is not square.
    pub fn charpoly(&self, x: Symbol) -> MatrixResult<Term<T>> {
        let set = *self.set.get_set();
        let coefficients = self.charpoly_coefficients()?;
        let degree = coefficients.len() - 1;
        let x = Term::Symbol(SymbolTerm::new(x, set));
        let exponant_set = set.get_exponant_set();
        Ok(coefficients
            .into_iter()
            .enumerate()
            .fold(Term::zero(set), |res, (i, coefficient)| {
                res + coefficient
                    * x.pow(&Term::constant(
                        exponant_set.nth((degree - i) as i64),
                        exponant_set,
                    ))
            }))
    }
}
