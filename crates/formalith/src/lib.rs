//! Formalith is a computer algebra system, generic over the algebraic structure
//! (set, group, ring, field...) expressions live in.
//!
//! ```
//! use formalith::{field::real::R, parse, term::Expand};
//!
//! assert_eq!(parse!("(x+1)^2", R).expand(), parse!("x^2+2*x+1", R));
//! ```

// Enable some additional lints for code and documentation clarity
#![warn(
    rustdoc::all,
    missing_docs,
    clippy::cargo,
    clippy::pedantic,
    clippy::nursery
)]
// This lint is not relevant in most cases
#![allow(clippy::or_fun_call)]
// Allow this lint since it cause a stack overflow in clippy, probably due to infinite types.
// A bug report should probably be filled
#![allow(clippy::significant_drop_in_scrutinee)]
// Specialization is incomplete
#![allow(incomplete_features)]
#![feature(specialization)]

/// A profiling scope named `$name`, optionally with dynamic `$data`, lasting until the end of the enclosing block.
/// Nothing without the feature `profile`; recorded by the backend of the `profiling` crate enabled by the
/// application.
macro_rules! profile_scope {
    ($name:expr $(, $data:expr)?) => {
        #[cfg(feature = "profile")]
        profiling::scope!($name $(, $data)?);
    };
}

pub mod combinatorics;
pub mod context;
pub mod dynamic;
pub mod field;
pub mod integrate;
mod iter;
pub mod limit;
pub mod matrix;
pub mod ode;
pub mod parser;
pub mod polynom;
pub mod printer;
pub mod solve;
pub mod sum;
pub mod term;
pub mod traits;
