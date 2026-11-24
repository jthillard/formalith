//! Iterator helpers replacing unstable standard library methods.

use std::cmp::Ordering;

/// Lexicographically compares two iterators using `cmp`, like the unstable `Iterator::cmp_by`.
pub fn cmp_by<A, B>(
    a: impl IntoIterator<Item = A>,
    b: impl IntoIterator<Item = B>,
    mut cmp: impl FnMut(A, B) -> Ordering,
) -> Ordering {
    partial_cmp_by(a, b, |a, b| Some(cmp(a, b))).unwrap_or(Ordering::Equal)
}

/// Lexicographically compares two iterators using `partial_cmp`, like the unstable `Iterator::partial_cmp_by`.
pub fn partial_cmp_by<A, B>(
    a: impl IntoIterator<Item = A>,
    b: impl IntoIterator<Item = B>,
    mut partial_cmp: impl FnMut(A, B) -> Option<Ordering>,
) -> Option<Ordering> {
    let mut b = b.into_iter();
    for a in a {
        let Some(b) = b.next() else {
            return Some(Ordering::Greater);
        };
        match partial_cmp(a, b) {
            Some(Ordering::Equal) => {}
            non_eq => return non_eq,
        }
    }
    Some(if b.next().is_some() {
        Ordering::Less
    } else {
        Ordering::Equal
    })
}
