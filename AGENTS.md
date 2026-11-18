# AGENTS.md

Formalith is a computer algebra system library in Rust, generic over the algebraic structure (set/group/ring/field) expressions live in.

## Commands

Nightly Rust is required (`#![feature(specialization)]`); `rust-toolchain.toml` pins it, so plain `cargo` works.

- `cargo build`, `cargo test` (unit, `tests/`, doctests), e.g. `cargo test --test parser test_try_parse`
- `cargo run` runs `src/main.rs`, a scratch binary for manual experiments.
- `cargo run --bin cli [expr...]`: REPL (`--set <name>` / `:set <name>`, `--typst` / `:typst`). Needs the default `cli` feature (pulls `rustyline`).
- Do not run `cargo clippy`: it hangs on this crate's recursive types. Verify with `cargo build` / `cargo test`. The crate still warns on `clippy::pedantic`, `nursery`, `cargo`, `missing_docs` and `rustdoc::all`, so every public item needs a doc comment.
- `make web` builds the wasm package into `web/www/pkg/` (needs `wasm-pack` and the `wasm32-unknown-unknown` target), `make web-serve` serves it on port 8000. `wasm-bindgen` is pinned in `web/Cargo.toml` to the installed CLI version.
- `cargo doc`: doc comments can contain Typst math as `{$ ... $}`, rendered by `docs/typstts.html` (injected by `.cargo/config.toml`).

## Architecture

**Sets** (`src/field/`). Expressions are `Term<T>` with `T: Set` a small `Copy` value describing the structure, used as a constant: `parse!("x^2", R)`. Hierarchy: `Set` → `PartiallyOrderedSet` → `Group` → `Ring` → `EuclideanRing` / `Field` / `Derivable`. Each set declares its `Element`, an `ExponantSet` (where powers live) and a `ProductCoefficientSet` (coefficient of `Mul`). Concrete sets in `src/field/commons/`:
- `N` (ordering only, no arithmetic), `Z`, `R` (rationals via `malachite`)
- `C`: Gaussian rationals over `CartesianPower<R, 2>`; the identifier `i` parses as the imaginary unit. `CartesianPower<T, K>` is only a componentwise group.
- `M`: matrices, with symbolic entries (`M<TermSet<R>>`)
- `Zn`: `Z/nZ` with a runtime modulus and `u64` representatives; `factor` works on univariate polynomials when `n` is prime.
- `Poly<K>`: `K[x]` (`K.get_polynomial_ring(symbol!("x"))`). Values are whole expanded `MultivariatePolynomial`s, the variable parses as a value, other identifiers stay symbols. `gcd`/`lcm`/`quo`/`rem` are evaluated, `factor` is not (products of values fold back).

**Terms** (`src/term/`). `Term<T>` is an enum `Value | Symbol | Add | Mul | Pow | Fun`. `Fun` holds `Box<dyn Function<T>>`, so a function's arguments may live in another set than its result (`det` takes matrices, returns scalars). `TermSet<T>` (`term_ring.rs`) is the set whose elements are `Term<T>`s; it makes coefficients symbolic, hence types like `Term<M<TermSet<R>>>`.

**Normalize / Expand / Simplify.** Traits on `Term<T>` using specialization: a `default fn` for plain `Set` (often `todo!()`, so missing structure panics at runtime, not compile time) and real impls for `Ring`. Set-specific rules hook in through `Ring::normalize` / `expand` / `simplify` (e.g. `real.rs`, `matrix.rs`). Terms carry a `NORMALIZED` flag (`term/flags.rs`) to skip re-normalization.

**Parser** (`src/parser/`). Pratt parser, entry points `parse!` / `try_parse!`. Dispatched per set via `SetParseExpression` (`parse_literal`, optional `parse_expression` for e.g. matrix literals `[[a, b], [c, d]]`). Its `MatrixArgumentSet` is the set `det(...)` arguments parse in (`M<TermSet<Self>>` for scalar sets, `Self` for matrix sets); it must never build a bigger set from a matrix set, or the parser is monomorphized over infinitely many types. Sets without `SetParseExpression` fail at runtime.

**Definitions** (`src/parser/environment.rs`). `a := ...` / `f(x, y) := ...` (`Parser::parse_statement`, `Environment::eval`). An `Environment` stores definitions as source text plus a snapshot of the definitions existing when they were made (so no recursion, redefinitions don't affect earlier definitions), and the parser expands them in the outermost set (`Parser::with_environment`, `parse!(input, set, &env)`), so they work in any set. Arguments are passed by name (re-parsed at each use). Names a set reserves (`i`, a polynomial variable) are declared by `SetParseExpression::is_constant`.

**Solving** (`src/solve/`). A statement of comma-separated equations, like `x + y = 3, x - y = 1`, is solved for all its symbols; `solve(a*x + y = 1, x - y = b, x, y)` solves for the listed symbols, the others being parameters (`Statement::System`, parsed by `Parser::parse_statement`; `solve` is a builtin only allowed as a whole statement). Entry point is the `Solve` trait: `solve` (every symbol, sorted by name) calls `solve_for`, specialized (unsupported by default and for `M`, real impl for rings). It expands `lhs - rhs` and currently only tries `linear::solve`: coefficients are extracted as terms (`Term::symbols` tells which parts contain unknowns), then Gaussian elimination with `Matrix::row_reduce_left` (pivots only in the coefficient columns) runs in the set itself when every coefficient is a value (so pivots must be invertible, `2*x = 4` fails in `Z`), or in `TermSet` otherwise, assuming symbolic pivots are non-zero, with results simplified. New strategies (polynomial equations...) belong in the ring impl of `Solve::solve_for`. A `Solution` gives pivot unknowns in terms of free unknowns, or `no solution`.

**Symbols** (`src/context/`). `Symbol` is a `usize` id interned in a global `RwLock<Context>`; create with `symbol!("x")`. Builtins have fixed ids from `Context::BUILTIN_NAMES`: append new ones at the end, and set their arity in `Context::builtin_arity` (one argument by default; checked by the parser). Builtins are evaluated in the set's `normalize` (e.g. `R::eval_builtin`).

**Other modules.** `polynom/`: `MultivariatePolynomial` (gcd, division, square-free factorization; full factorization over ℚ in `polynom/factor/`: Zassenhaus univariate, Wang/EEZ multivariate, modular and Gaussian variants), converted with `Term::to_polynomial` / `ToTerm`. `matrix/`: generic `Matrix<T>` (det, inverse, row reduction). `printer/`: `Print` (one line), `PrettyPrint` (2D layout), and Typst output via `PrintOptions::typst()`.

**REPL and web.** `src/repl.rs` (`SetChoice`, `sets_help`) holds the evaluation logic shared by `src/bin/cli.rs` and `web/` (`formalith-web` workspace member, `wasm-bindgen` cdylib exporting `evaluate`, `set_name`, `sets_help`). `web/www/` is a static terminal-like page: evaluation runs in a module Web Worker, results are printed as Typst and rendered to SVG with typst.ts from jsdelivr. Panics abort the wasm instance, so the page replaces the worker after one (also how Ctrl+C works).

## Quirks

- `#![allow(clippy::significant_drop_in_scrutinee)]` exists because that lint overflows clippy's stack.
- Feature `concise-debug` replaces derived `Debug` on terms with a compact form.
