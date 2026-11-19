//! Hermite and Smith normal forms of matrices over a Euclidean ring, like `{$ZZ$}`.

use crate::field::EuclideanRing;

use super::Matrix;

/// Row operations applied to a matrix and to the matrix accumulating them.
struct Tracked<'a, T: EuclideanRing> {
    matrix: &'a mut Matrix<T>,
    transform: &'a mut Matrix<T>,
}

impl<T: EuclideanRing> Tracked<'_, T> {
    fn swap(&mut self, a: usize, b: usize, rows: bool) {
        if a == b {
            return;
        }
        if rows {
            self.matrix.swap_rows(a, b);
            self.transform.swap_rows(a, b);
        } else {
            self.matrix.swap_columns(a, b);
            self.transform.swap_columns(a, b);
        }
    }

    fn add(&mut self, target: usize, source: usize, factor: &T::Element, rows: bool) {
        if rows {
            self.matrix.row_add(target, source, factor);
            self.transform.row_add(target, source, factor);
        } else {
            self.matrix.column_add(target, source, factor);
            self.transform.column_add(target, source, factor);
        }
    }

    fn scale(&mut self, line: usize, unit: &T::Element) {
        self.matrix.scale_row(line, unit);
        self.transform.scale_row(line, unit);
    }

    /// The entry of the `line`th row (or column) at `position`.
    fn entry(&self, line: usize, position: usize, rows: bool) -> &T::Element {
        if rows {
            &self.matrix[(line, position)]
        } else {
            &self.matrix[(position, line)]
        }
    }

    /// Cancel the entry at `position` of the line `other` with unimodular operations between the lines `pivot`
    /// and `other` (rows if `rows`, columns otherwise), by the Euclidean algorithm. The entry of `pivot` ends up
    /// being their greatest common divisor, up to a unit. The line `pivot` is left unchanged when its entry
    /// divides the other one, so that the Smith form doesn't refill lines it cleared.
    fn euclid(&mut self, pivot: usize, other: usize, position: usize, rows: bool) {
        let set = self.matrix.set;
        while !set.is_zero(self.entry(other, position, rows)) {
            if set.is_zero(self.entry(pivot, position, rows)) {
                self.swap(pivot, other, rows);
                continue;
            }
            let (quotient, _) = set.quot_rem(
                self.entry(other, position, rows),
                self.entry(pivot, position, rows),
            );
            self.add(other, pivot, &set.neg(&quotient), rows);
            if !set.is_zero(self.entry(other, position, rows)) {
                self.swap(pivot, other, rows);
            }
        }
    }
}

impl<T: EuclideanRing> Matrix<T> {
    /// The row style Hermite normal form `H` of the matrix, with a unimodular `U` such that `{$U A = H$}`, and the
    /// rank of `A`. `H` is in row echelon form, pivots are normalized (positive in `{$ZZ$}`) and the entries
    /// above pivots are reduced modulo them (in `{$[0, p)$}` in `{$ZZ$}`).
    #[must_use]
    pub fn hermite_decomposition(&self) -> (Self, Self, usize) {
        self.hermite_decomposition_left(self.width())
    }

    /// [`Matrix::hermite_decomposition`] with pivots in the first `columns` columns only, like the coefficients of
    /// an augmented matrix. The returned rank is the rank of these columns.
    #[must_use]
    pub fn hermite_decomposition_left(&self, columns: usize) -> (Self, Self, usize) {
        let set = self.set;
        let mut matrix = self.clone();
        let mut transform = Self::identity(self.height(), set);
        let mut tracked = Tracked {
            matrix: &mut matrix,
            transform: &mut transform,
        };
        let mut pivot_row = 0;
        for column in 0..columns.min(self.width()) {
            if pivot_row >= self.height() {
                break;
            }
            for row in pivot_row + 1..self.height() {
                tracked.euclid(pivot_row, row, column, true);
            }
            let pivot = tracked.matrix[(pivot_row, column)].clone();
            if set.is_zero(&pivot) {
                continue;
            }
            let unit = set.normal_unit(&pivot);
            if !set.is_one(&unit) {
                tracked.scale(pivot_row, &unit);
            }
            let pivot = tracked.matrix[(pivot_row, column)].clone();
            for row in 0..pivot_row {
                let (quotient, _) = set.quot_rem(&tracked.matrix[(row, column)], &pivot);
                if !set.is_zero(&quotient) {
                    tracked.add(row, pivot_row, &set.neg(&quotient), true);
                }
            }
            pivot_row += 1;
        }
        (transform, matrix, pivot_row)
    }

    /// The Hermite normal form of the matrix, see [`Matrix::hermite_decomposition`].
    #[must_use]
    pub fn hermite(&self) -> Self {
        self.hermite_decomposition().1
    }

    /// The Smith normal form `D` of the matrix, with unimodular `U` and `V` such that `{$U A V = D$}`. `D` is
    /// diagonal, its diagonal entries `d_i` are normalized (non-negative in `{$ZZ$}`) and `d_i` divides `d_(i+1)`.
    #[must_use]
    pub fn smith_decomposition(&self) -> (Self, Self, Self) {
        let set = self.set;
        let (height, width) = (self.height(), self.width());
        let mut matrix = self.clone();
        let mut left = Self::identity(height, set);
        let mut right = Self::identity(width, set);
        for t in 0..height.min(width) {
            loop {
                // Move a non-zero entry to `(t, t)`
                let Some((i, j)) = (t..height)
                    .flat_map(|i| (t..width).map(move |j| (i, j)))
                    .find(|&index| !set.is_zero(&matrix[index]))
                else {
                    return (left, matrix, right);
                };
                Tracked {
                    matrix: &mut matrix,
                    transform: &mut left,
                }
                .swap(t, i, true);
                Tracked {
                    matrix: &mut matrix,
                    transform: &mut right,
                }
                .swap(t, j, false);
                // Clear the column and the row of the pivot, until both are cleared (each one can fill the other)
                loop {
                    let mut rows = Tracked {
                        matrix: &mut matrix,
                        transform: &mut left,
                    };
                    for i in t + 1..height {
                        rows.euclid(t, i, t, true);
                    }
                    let mut columns = Tracked {
                        matrix: &mut matrix,
                        transform: &mut right,
                    };
                    for j in t + 1..width {
                        columns.euclid(t, j, t, false);
                    }
                    if (t + 1..height).all(|i| set.is_zero(&matrix[(i, t)])) {
                        break;
                    }
                }
                // The pivot must divide the remaining entries, otherwise add their row and start again
                let pivot = matrix[(t, t)].clone();
                let not_divided = (t + 1..height).find(|&i| {
                    (t + 1..width).any(|j| !set.is_zero(&set.rem(&matrix[(i, j)], &pivot)))
                });
                match not_divided {
                    Some(i) => Tracked {
                        matrix: &mut matrix,
                        transform: &mut left,
                    }
                    .add(t, i, &set.one(), true),
                    None => break,
                }
            }
            let unit = set.normal_unit(&matrix[(t, t)]);
            if !set.is_one(&unit) {
                Tracked {
                    matrix: &mut matrix,
                    transform: &mut left,
                }
                .scale(t, &unit);
            }
        }
        (left, matrix, right)
    }

    /// The Smith normal form of the matrix, see [`Matrix::smith_decomposition`].
    #[must_use]
    pub fn smith(&self) -> Self {
        self.smith_decomposition().1
    }
}
