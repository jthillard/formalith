//! Expressions over the natural integers `N`.
use std::cmp::Ordering;

use formalith::{
    field::{PartiallyOrderedSet, natural::N},
    parse, try_parse,
};
use malachite::Natural;

mod common;
use common::line;

#[test]
fn constants() {
    assert_eq!(line(&parse!("5", N)), "5");
    assert_eq!(
        line(&parse!("100000000000000000000", N)),
        "100000000000000000000"
    );
}

#[test]
fn symbols() {
    assert_eq!(line(&parse!("x", N)), "x");
}

#[test]
fn errors() {
    assert!(try_parse!("", N).is_err());
    assert!(try_parse!("5.5", N).is_err());
    assert!(try_parse!("-5", N).is_err());
    assert!(try_parse!("2+3", N).is_err());
}

#[test]
fn ordering() {
    assert_eq!(
        N.partial_cmp(&Natural::from(2u32), &Natural::from(3u32)),
        Some(Ordering::Less)
    );
}
