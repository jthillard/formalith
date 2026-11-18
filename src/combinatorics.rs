//! Combinatorics iterators and functions

use malachite::{
    Integer,
    base::num::basic::traits::{One, Zero},
    integer::exhaustive::integer_increasing_inclusive_range,
};

/// Iterator over the weak compositions of `k` into `n` parts.
///
/// ```
/// use formalith::combinatorics::CompositionIterator;
///
/// let mut iterator = CompositionIterator::new(3, 2);
/// let mut compositions = vec![];
/// while let Some(composition) = iterator.next_composition() {
///     compositions.push(composition.to_vec());
/// }
/// assert_eq!(
///     compositions,
///     [[2, 0, 0], [1, 1, 0], [1, 0, 1], [0, 2, 0], [0, 1, 1], [0, 0, 2]]
/// );
/// ```
pub struct CompositionIterator {
    indices: Vec<usize>,
    k: usize,
    init: bool,
}

impl CompositionIterator {
    /// Create a new composition iterator.
    #[must_use]
    pub fn new(n: usize, k: usize) -> Self {
        Self {
            indices: vec![0; n],
            k,
            init: false,
        }
    }

    /// Yield the next composition.
    pub fn next_composition(&mut self) -> Option<&[usize]> {
        if self.indices.is_empty() {
            return None;
        }

        if !self.init {
            self.init = true;
            self.indices[0] = self.k;
            return Some(&self.indices);
        }

        if self.k == 0 {
            return None;
        }

        let mut i = self.indices.len() - 1;
        while self.indices[i] == 0 {
            i -= 1;
        }

        let mut last_value = 0;
        if i == self.indices.len() - 1 {
            // End of the vector was reached
            last_value = self.indices[i];
            self.indices[i] = 0;

            if self.indices.len() == 1 {
                return None;
            }

            i -= 1;
            while self.indices[i] == 0 {
                if i == 0 {
                    return None;
                }

                i -= 1;
            }
        }

        self.indices[i] -= 1;
        self.indices[i + 1] = last_value + 1;

        Some(&self.indices)
    }
}

/// General trait to do combinatorics on any integer type.
pub trait Combinatorics: Sized {
    /// Compute a Newton binomial
    fn binom(n: Self, k: Self) -> Self;
    /// Compute a Newton multinomial
    fn multinom(k: &[Self]) -> Self;
}

impl Combinatorics for Integer {
    fn binom(n: Self, mut k: Self) -> Self {
        if n < 0 || k < 0 || k > n {
            return Self::ZERO;
        }

        if k > &n / Self::from(2) {
            k = &n - &k;
        }

        if k == 0 {
            return Self::ONE;
        }

        let mut result = Self::ONE;
        for i in integer_increasing_inclusive_range(Self::ONE, k.clone()) {
            result *= &n - &k + &i;
            result /= &i;
        }
        result
    }

    fn multinom(k: &[Self]) -> Self {
        let mut result = Self::ONE;
        let mut acc = Self::ZERO;

        for value in k {
            acc += value;
            result *= Self::binom(acc.clone(), value.clone());
        }

        result
    }
}

/// Advance `indices`, a strictly increasing combination of `indices.len()` elements among `0..n`, to the
/// next one in lexicographic order. Returns `false`, leaving `indices` unchanged, after the last one.
pub fn next_combination(indices: &mut [usize], n: usize) -> bool {
    let k = indices.len();
    for i in (0..k).rev() {
        if indices[i] < n - k + i {
            indices[i] += 1;
            for j in i + 1..k {
                indices[j] = indices[j - 1] + 1;
            }
            return true;
        }
    }
    false
}
