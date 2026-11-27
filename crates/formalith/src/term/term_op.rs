//! Implementation of operations over [Term].

use std::cmp::Ordering;

use super::{Add, Mul, Pow, Term};
use crate::{
    field::{Group, Monoid, Ring, Semiring},
    term::{Normalize, flags::Flags},
};

impl<T: Monoid> std::ops::Add for &Term<T> {
    type Output = Term<T>;

    fn add(self, rhs: Self) -> Self::Output {
        debug_assert!(!self.needs_normalization(), "{self:#?}");
        debug_assert!(!rhs.needs_normalization());
        let ring = self.get_set();
        if let Term::Add(a1) = self {
            if let Term::Add(a2) = rhs {
                // Merge both sorted sums
                let mut res = Add::with_capacity(a1.len() + a2.len(), ring);
                let mut a1_iter = a1.iter();
                let mut a2_iter = a2.iter();
                let mut a1_cursor = a1_iter.next();
                let mut a2_cursor = a2_iter.next();
                loop {
                    match (a1_cursor, a2_cursor) {
                        (Some(a1), Some(a2)) => match a1.cmp_terms(a2) {
                            Ordering::Less => {
                                res.push(a1.clone());
                                a1_cursor = a1_iter.next();
                            }
                            Ordering::Equal => {
                                let mut merged = a1.clone();
                                let has_merged = merged.try_merge_terms(a2);
                                if !merged.is_zero() {
                                    res.push(merged);
                                }
                                if !has_merged {
                                    res.push(a2.clone());
                                }
                                a1_cursor = a1_iter.next();
                                a2_cursor = a2_iter.next();
                            }
                            Ordering::Greater => {
                                res.push(a2.clone());
                                a2_cursor = a2_iter.next();
                            }
                        },
                        (Some(a1), None) => {
                            res.push(a1.clone());
                            a1_cursor = a1_iter.next();
                        }
                        (None, Some(a2)) => {
                            res.push(a2.clone());
                            a2_cursor = a2_iter.next();
                        }
                        (None, None) => break,
                    }
                }
                match res.len() {
                    0 => Term::zero(ring),
                    1 => res.terms.pop().unwrap(),
                    _ => {
                        res.set_normalized(true);
                        Term::Add(res)
                    }
                }
            } else {
                let mut a1_clone = a1.clone();
                if !rhs.is_zero() {
                    match a1_clone
                        .terms
                        .binary_search_by(|value| value.cmp_terms(rhs))
                    {
                        Ok(i) => {
                            if !a1_clone.terms[i].try_merge_terms(rhs) {
                                a1_clone.terms.insert(i, rhs.clone());
                            } else if a1_clone.terms[i].is_zero() {
                                a1_clone.terms.remove(i);
                            }
                        }
                        Err(i) => a1_clone.terms.insert(i, rhs.clone()),
                    }
                }
                if a1_clone.len() == 1 {
                    a1_clone.terms[0].clone()
                } else {
                    Term::Add(a1_clone)
                }
            }
        } else if let Term::Add(_) = rhs {
            rhs.add(self)
        } else {
            let mut self_clone = self.clone();
            if self_clone.try_merge_terms(rhs) {
                self_clone
            } else {
                Term::Add(Add::new(
                    if self_clone.cmp_terms(rhs) == Ordering::Greater {
                        vec![rhs.clone(), self_clone]
                    } else {
                        vec![self_clone, rhs.clone()]
                    },
                    ring,
                ))
                .normalize()
            }
        }
    }
}

impl<T: Monoid> std::ops::AddAssign<&Self> for Term<T> {
    fn add_assign(&mut self, rhs: &Self) {
        *self = &*self + rhs;
    }
}

impl<T: Monoid> std::ops::AddAssign for Term<T> {
    fn add_assign(&mut self, rhs: Self) {
        *self = &*self + &rhs;
    }
}

impl<T: Monoid> std::ops::Add<&Self> for Term<T> {
    type Output = Self;

    fn add(self, rhs: &Self) -> Self::Output {
        &self + rhs
    }
}

impl<T: Monoid> std::ops::Add for Term<T> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        &self + &rhs
    }
}

impl<T: Semiring> std::ops::Mul for &Term<T> {
    type Output = Term<T>;

    fn mul(self, rhs: Self) -> Self::Output {
        debug_assert!(!self.needs_normalization());
        debug_assert!(!rhs.needs_normalization());
        Term::Mul(Mul::new(
            self.get_set().get_coefficient_set().nth(1),
            vec![self.clone(), rhs.clone()],
            self.get_set(),
        ))
        // Unlike sums, products are normalized again rather than merged: sets hook rules into products (radicals
        // and `exp` in `R`, values folded into the coefficient in rings), which a merge of the factors would skip
        .normalize()
    }
}

impl<T: Semiring> std::ops::MulAssign<&Self> for Term<T> {
    fn mul_assign(&mut self, rhs: &Self) {
        *self = &*self * rhs;
    }
}

impl<T: Semiring> std::ops::MulAssign for Term<T> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = &*self * &rhs;
    }
}

impl<T: Semiring> std::ops::Mul<&Self> for Term<T> {
    type Output = Self;

    fn mul(self, rhs: &Self) -> Self::Output {
        &self * rhs
    }
}

impl<T: Semiring> std::ops::Mul for Term<T> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        &self * &rhs
    }
}

impl<T: Ring> std::ops::Div for &Term<T> {
    type Output = Term<T>;

    fn div(self, rhs: Self) -> Self::Output {
        debug_assert!(!self.needs_normalization());
        debug_assert!(!rhs.needs_normalization());
        self * &rhs
            .pow(&Term::nth(-1, self.get_set().get_exponant_set()))
            .normalize()
    }
}

impl<T: Ring> std::ops::DivAssign for Term<T> {
    fn div_assign(&mut self, rhs: Self) {
        *self = &*self / &rhs;
    }
}

impl<T: Ring> std::ops::Div<&Self> for Term<T> {
    type Output = Self;

    fn div(self, rhs: &Self) -> Self::Output {
        &self / rhs
    }
}

impl<T: Ring> std::ops::Div for Term<T> {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        &self / &rhs
    }
}

impl<T: Group> std::ops::Neg for Term<T> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        -&self
    }
}

impl<T: Group> std::ops::Neg for &Term<T> {
    type Output = Term<T>;

    fn neg(self) -> Self::Output {
        debug_assert!(!self.needs_normalization());
        let mut new = self.clone();
        match new {
            Term::Value(ref mut value) => value.set.neg_assign(&mut value.value),
            Term::Mul(ref mut mul) => {
                let coeff = mul.get_coeff();
                mul.set_coeff(mul.set.get_coefficient_set().neg(&coeff));
            }
            Term::Add(_) | Term::Symbol(_) | Term::Pow(_) | Term::Fun(_) => {
                let set = new.get_set();
                new = Term::Mul(Mul::new(set.get_coefficient_set().nth(-1), vec![new], set))
                    .normalize();
            }
        }
        new
    }
}

impl<T: Group> std::ops::Sub for &Term<T> {
    type Output = Term<T>;

    fn sub(self, rhs: Self) -> Self::Output {
        debug_assert!(!self.needs_normalization());
        debug_assert!(!rhs.needs_normalization());
        self + &-rhs
    }
}

impl<T: Group> std::ops::SubAssign for Term<T> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = &*self - &rhs;
    }
}

impl<T: Group> std::ops::Sub<&Self> for Term<T> {
    type Output = Self;

    fn sub(self, rhs: &Self) -> Self::Output {
        &self - rhs
    }
}

impl<T: Group> std::ops::Sub for Term<T> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        &self - &rhs
    }
}

impl<T: Semiring> Term<T> {
    /// Compute `self^exponant`
    #[must_use]
    pub fn pow(&self, exponant: &Term<T::ExponantSet>) -> Self {
        debug_assert!(!self.needs_normalization());
        debug_assert!(!exponant.needs_normalization());
        let res = Self::Pow(Pow::new(self.clone(), exponant.clone(), self.get_set()));
        res.normalize()
    }
}
