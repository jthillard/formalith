//! Integration tests, as modules of a single test binary: each binary links the whole library (about 80 MB with
//! debug information), so one binary per file made `cargo test` write gigabytes and spend most of its time on disk.
//! Run one file with a filter, `cargo test -p formalith --test integration parser::`.

mod common;

mod approx;
mod arithmetic;
mod assumptions;
mod check_approx;
mod check_assumptions;
mod check_complex;
mod check_cross_set;
mod check_docs;
mod check_dsolve;
mod check_gamma;
mod check_helpers;
mod check_inequality;
mod check_integrate;
mod check_limit;
mod check_matrix;
mod check_number_theory;
mod check_optimize;
mod check_poly_ring;
mod check_rewrite;
mod check_roundtrip;
mod check_series;
mod check_solve;
mod check_sum;
mod check_whole_series;
mod combinatorics;
mod complex;
mod definitions;
mod dsolve;
mod dynamic;
mod expand;
mod functions;
mod integer;
mod integrate;
mod limit;
mod matrix;
mod modular;
mod natural;
mod optimize;
mod parser;
mod polynomial;
mod polynomial_ring;
mod printer;
mod series;
mod solve;
mod soundness;
mod sum;
mod syntax;
