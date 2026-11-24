//! Holonomic (D-finite) functions: functions satisfying a linear differential equation with polynomial
//! coefficients, whose Taylor coefficients satisfy a linear recurrence with polynomial coefficients.
//!
//! [`dfinite::annihilator`] derives the differential equation of an expression exactly, by closure properties
//! ([`ore`]), and [`recurrence::Recurrence`] turns it into the recurrence of the coefficients, which proves a
//! guessed closed form of the general term of the series. Used by `series(f, x, a, oo)`.

pub mod dfinite;
pub mod ore;
pub mod ratfun;
pub mod recurrence;
