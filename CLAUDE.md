# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

Formalith is a computer algebra system (CAS) library in Rust, generic over the algebraic structure (set/group/ring/field) that expressions live in. `src/main.rs` is a scratch binary for manual experiments, not a real CLI.

## Toolchain and commands

Nightly Rust is required: `src/lib.rs` enables `#![feature(specialization, iter_order_by)]`. `rust-toolchain.toml` pins the `nightly` channel, so plain `cargo` commands work.

- Build: `cargo build`
- Run scratch binary: `cargo run`
- All tests (unit, `tests/`, doctests): `cargo test`
- Single test: `cargo test --test parser test_try_parse`
- Doctests only: `cargo test --doc`
- Lint: `cargo clippy` — the crate warns on `clippy::pedantic`, `clippy::nursery`, `clippy::cargo`, `missing_docs` and `rustdoc::all`, so every public item needs a doc comment.
- Coverage (needs `cargo-llvm-cov`): `make coverage`, `make coverage-html`
- Docs: `cargo doc` — `.cargo/config.toml` injects `docs/typstts.html`, which renders Typst math written in doc comments as `{$ ... $}`.
- Feature `concise-debug`: replaces derived `Debug` on terms with a compact form.

## Architecture

**Sets drive everything** (`src/field/`). An expression type is `Term<T>` where `T: Set` is a zero-sized-ish `Copy` value describing the algebraic structure. Trait hierarchy: `Set` → `PartiallyOrderedSet` → `Group` → `Ring` → `EuclideanRing` / `Field` / `Derivable`. Each `Set` declares its `Element` type plus an `ExponantSet` (where powers live) and `ProductCoefficientSet` (coefficient of `Mul`). Concrete sets in `src/field/commons/`: `Z` (integers), `R` (rationals via `malachite`), `M` (matrices). Sets are used as constants: `parse!("x^2", R)`.

**Terms** (`src/term/`). `Term<T>` is an enum: `Value`, `Symbol`, `Add`, `Mul`, `Pow`, `Fun`. `Fun` holds `Box<dyn Function<T>>` (dyn-clone/eq/hash) so a function can take arguments from a different set than its result (e.g. `det` takes matrices, returns reals). Operator overloads are in `term_op.rs`.

**`TermSet<T>`** (`term_ring.rs`) is the set whose elements are whole `Term<T>`s. It makes coefficients symbolic: matrices are `M<TermSet<R>>`, and polynomial/exponent sets are often `TermSet<...>`. Expect nested generic types like `Term<M<TermSet<R<Rational>>>>`.

**Normalization / Expand / Simplify.** `Normalize`, `Expand` traits on `Term<T>` use specialization: a `default fn` (often `todo!()`) for plain `Set`, and real impls for `Ring` etc. Ring-specific rewrite rules hook in through `Ring::normalize`, `Ring::expand`, `Ring::simplify` (see `R::normalize` in `real.rs`, `M::expand` / `M::simplify` in `matrix.rs`). Terms carry a `NORMALIZED` bit flag (`term/flags.rs`) to skip re-normalizing.

**Parser** (`src/parser.rs`, `parser/lexer.rs`). Pratt-style parser; entry points are the `parse!` / `try_parse!` macros. Parsing is dispatched per set through `SetParseExpression<N>` (`parse_literal`, optional custom `parse_expression`, e.g. matrix literals `[[a, b], [c, d]]`). `N` is a `typenum` recursion-depth counter so parsing a function argument in another set (like `det(...)`) is type-level bounded; nesting beyond 10 levels fails.

**Symbols** (`src/context/`). `Symbol` is a `usize` id interned in a global `RwLock<Context>`; data stored in an `AppendOnlyVec`. Built-in function symbols are fixed ids: `Context::ABS = 0`, `Context::DET = 1` (order of `BUILTIN_NAMES` matters). Create symbols with `symbol!("x")`.

**Other modules.** `polynom/`: `MultivariatePolynomial` (gcd, quotient/remainder, square-free factorization; complete factorization over ℚ in `polynom/factor/` with Zassenhaus for univariate and Wang/EEZ lifting for multivariate, falling back to square-free when coefficients aren't rational), converted from/to terms via `Term::to_polynomial` and `ToTerm`. `matrix/`: generic `Matrix<T: Set>` (det, inverse, row reduction). `printer/`: `Print` (single-line) and `PrettyPrint` (2D box layout via `PrettyPrinter`), colored with `owo-colors`. `combinatorics.rs`: composition iterators used by expansion.

## Known quirks

- `#![allow(clippy::significant_drop_in_scrutinee)]` exists because that lint overflows clippy's stack on this crate's recursive types.
- Many `default fn` specialization fallbacks are `todo!()`: calling an operation on a set lacking the required structure panics at runtime, not compile time.
