# AGENTS.md

Formalith is a computer algebra system library in Rust, generic over the algebraic structure (set / group / ring /
field) expressions live in. `CLAUDE.md` is a symlink to this file. `ROADMAP.md` lists known gaps; user-facing
behavior of each builtin is documented in `crates/formalith/src/context/docs.rs`.

## Crates (`crates/`)

- `formalith`: the CAS library. Paths below like `src/...` are relative to `crates/formalith/`.
- `formalith-session`: interactive `Session` shared by the interfaces (commands, definitions, panics caught,
  `replay` lines restoring state), and `graph.rs` (graphs of a line, for the GUI).
- `formalith-cli`: binary `formalith`, the default `cargo run` (REPL, or evaluates its arguments).
- `formalith-web`: wasm web REPL (`www/`, session in a Web Worker, Typst rendered with typst.ts).
- `formalith-gui`: graphing calculator (egui / eframe / wgpu, native and wasm). Not a default member.
- `formalith-gui-worker`: wasm only, the GUI's Web Worker (`formalith-gui` without its `ui` feature).

## Commands

Nightly Rust is required (`#![feature(specialization)]`); `rust-toolchain.toml` pins it, so plain `cargo` works.

- Iterate with `cargo test -p formalith --test integration <filter>` (a few seconds after an edit, e.g.
  `parser::test_try_parse`). Use `cargo test --workspace` only for the final check.
- Cargo runs sharing the target directory wait for its lock: run them one after the other.
- `cargo clippy --workspace --all-targets` must stay warning-free, and CI runs `cargo fmt --all --check`.
  The crate warns on `clippy::pedantic`, `nursery`, `cargo`, `missing_docs` and `rustdoc::all`, so every public
  item needs a doc comment; crate-wide exceptions are in `src/lib.rs`, others are local `#[allow]`s with a comment.
- `cargo run [expr...]`: REPL (`--set <name>` / `:set <name>`, `--typst` / `:typst`, `help <builtin>`).
  For quick checks of behavior: `cargo run --release -- 'integrate(x e^x, x)'`, `cargo run -- --set 'Z/7' '...'`.
- Doc comments can contain Typst math as `{$ ... $}`, rendered by `docs/typstts.html` (injected by
  `.cargo/config.toml`).

`./dev <command> [--release] [--profile] [--serve] [-- args]` (`./dev --help`):

| Command   | Does                                                                                          |
|-----------|-----------------------------------------------------------------------------------------------|
| `repl`    | `cargo run -p formalith-cli`                                                                  |
| `gui`     | native GUI                                                                                    |
| `web`     | wasm REPL into `crates/formalith-web/www/pkg/` (needs `wasm-pack`), `--serve` on port 8000    |
| `gui-web` | GUI and worker into `crates/formalith-gui/www/`, `--serve` on port 8001                       |
| `docs`    | documentation page of builtins / sets / commands into `target/docs-site/`, port 8002          |
| `test`    | `cargo test --workspace`, args after `--` go to the test binaries                             |
| `fuzz`    | the ignored fuzzers; args after `--` replace the filter `fuzz` (e.g. `check_optimize::`)      |

`--release` is recommended for `fuzz` (profile `fuzz`: optimized but incremental). Without it, wasm builds skip
`wasm-opt`. `--profile` enables the puffin profiler (feature `profile`, `gui` / `gui-web` only, F12). Profiles are
in the root `Cargo.toml` (`dev` keeps line tables only, dependencies at `opt-level = 2`; `fuzz`; `wasm-release`).
`wasm-bindgen` is pinned in the wasm crates to the installed CLI version.

## Tests

- The files of `crates/formalith/tests/` are modules of one binary `integration` (`tests/main.rs`,
  `autotests = false`): add new test files as modules there.
- `tests/*.rs` compare results with hand-written ones. `tests/check_*.rs` check results against their definition
  (derivative of an antiderivative, substituted solutions, sampled regions, `approx` vs `Numeric`...) with the
  helpers of `tests/common/`: `harness::check_all` for curated cases (must not be skipped), `fuzz` for seeded
  random cases, `assert_pass` for regressions named `bug_*`.
- Fuzzers are `#[ignore]`d: `cargo test -p formalith --test integration check_optimize:: -- --ignored`, tuned with
  `FORMALITH_FUZZ_CASES`, `FORMALITH_SEED`, `FORMALITH_SHOW_SKIPPED`, `FORMALITH_TIMES`, `FORMALITH_WORKERS`.
  `.github/workflows/fuzz.yml` runs them nightly with a new seed.
- GPU tests of `formalith-gui` skip without an adapter.

## Core design

**Sets** (`src/field/`). Expressions are `Term<T>` with `T: Set` a small `Copy` value used as a constant:
`parse!("x^2", R)`. Hierarchy: `Set` → `PartiallyOrderedSet` → `Monoid` → `Group` / `Semiring`,
`Ring: Group + Semiring` → `EuclideanRing` / `Field` / `Derivable`. Term normalization, `+` and `*` need a
`Semiring`; `-`, `/`, `expand` and most features a `Ring`. Each set declares its `Element`, `ExponantSet` and
`ProductCoefficientSet`. Concrete sets in `src/field/commons/`:

- `N`, `Z`, `R` (exact rationals via `malachite`, plus symbolic constants; where calculus lives, `real/`),
- `C` (Gaussian rationals; calculus is done in `R` on real and imaginary parts, `complex/parts.rs`),
- `Zn` (`Z/nZ`, runtime modulus), `Poly<K>` (`K[x]`, `polynomial.rs`),
- `M` (matrices with symbolic entries, `M<TermSet<R>>`, also over `C`, `Z`, `Zn`; `matrix.rs`, `src/matrix/`),
- `CartesianPower<T, K>` (componentwise group, used by `C`).

**Terms** (`src/term/`). `Term<T>` is `Value | Symbol | Add | Mul | Pow | Fun`. `Fun` holds
`Box<dyn Function<T>>`, so arguments may live in another set (`det` takes matrices). `TermSet<T>`
(`term_ring.rs`) is the set whose elements are `Term<T>`s (symbolic coefficients). Flags (`term/flags.rs`):
`NORMALIZED` skips re-normalization, `APPROXIMATE` marks values from `approx`.

**Specialization.** Normalize / expand / simplify and most features are traits with a `default fn` for plain sets
(often `todo!()` or an "unsupported" error, so missing structure fails at runtime, not compile time) and real
impls for rings or for `R`. Set-specific parts go through specialized traits: `Solve`, `PolynomialRoots`,
`Transcendental`, `IntegerSystem`, `Assumed` (solve), `MatrixEntries`, `EigenSet` (matrices), `Optimize`,
`SolveInequality`, `Dsolve`. Set-specific rules hook into `Ring::normalize` / `expand` / `simplify`.

**Builtins** are evaluated during normalization: per set (`R::eval_builtin` in `real.rs`, `R::eval_calculus` for
`lim`, `series`, `integrate`, `sum`, `product`), then shared ring builtins in `fun::eval_ring_builtin`
(`src/term/fun.rs`). Calculus builtins stay unevaluated when unsupported.

**Statements.** `Parser::parse_statement` returns a `Statement`: an expression, a definition (`f(x) := ...`,
`src/parser/environment.rs`), a system (`x + y = 3, x - y = 1`, `solve(...)`), inequalities, `assume(...)`,
`argmin` / `extrema` / ..., or `dsolve(...)`. Sessions evaluate them in a set chosen at runtime through
`src/dynamic.rs` (`SetChoice`, `Evaluated`).

## Module map (`crates/formalith/src/`)

- `parser/`, `parser.rs`: Pratt parser (`parse!` / `try_parse!`), lexer, `environment.rs` (definitions stored as
  source text, expanded in the outermost set), `syntax.rs` (typesets the input without evaluating it). Per-set
  parsing via `SetParseExpression`.
- `context/`: interned `Symbol`s (`symbol!("x")`), builtin names / arities, `docs.rs` (builtin docs),
  `assumptions/` (linear assumptions, Fourier-Motzkin in `linear.rs`, installed thread-locally).
- `term/`: term operations, `derivative.rs`, `substitute.rs`, `relation.rs` (comparisons, `piecewise` conditions).
- `field/commons/real/`: the heart of `R`. `expr.rs` (shared shorthands for limits / series / integrals: use them
  rather than local copies), `sign.rs` (sign engine on assumptions), `approx.rs` (ball arithmetic in fixed point),
  `numeric.rs` (f64 compilation for graphs), `radicals.rs` (canonical radical sums in a tower), `rootof.rs`
  (real algebraic roots), `rewrite.rs` (`expand` / `simplify` rules, trigonometric zero proofs), `special.rs`
  (Gamma family, Lambert W, `piecewise`), `cases.rs` (case splits of calculus builtins on parameters).
- `solve/`: `linear.rs`, `polynomial.rs` (case splits, resultants), `lattice.rs` (`Z`, `Zn`), `inverse/`
  (transcendental equations), `inequality/` (CAD, at most 3 unknowns).
- `limit/`: Gruntz algorithm (`gruntz.rs`, `series.rs`), `expansion.rs` (`series`), `bounds.rs` (intervals).
- `integrate/`: `Integrator` search (`mod.rs`), `rational.rs`, `table.rs`, `substitution.rs`, `parts.rs`,
  `trig.rs`, `algebraic.rs`, `abs.rs`, `apart.rs`, `definite.rs`, `risch/` (transcendental Risch algorithm).
- `sum/`: antidifferences (`polynomial.rs`, `gosper.rs`), `zeilberger.rs`, `product.rs`, `taylor.rs` (whole
  series `series(f, x, a, oo)`), `field.rs` (coefficients in `QQ(t_1, ..., t_n)`).
- `holonomic/`: D-finite closure (`dfinite.rs`, `ore.rs`), recurrences, Petkovšek's *Hyper* (`hyper.rs`),
  algebraic towers (`algebraic.rs`).
- `ode/`: `dsolve` (first order, linear with constant coefficients, series solutions).
- `optimize/`: `argmin`, local extrema (`univariate.rs`, `multivariate.rs`, `domain.rs`).
- `polynom/`: `MultivariatePolynomial`, factorization (`factor/`), dense univariate `Poly` (`dense.rs`), nested
  fractions `Elem` (`fraction.rs`, shared by Risch and sums), real root isolation (`real_roots.rs`).
- `matrix/`: generic `Matrix<T>`, `linalg.rs`, `normal_form.rs` (Hermite, Smith), `eigen.rs`.
- `printer/`: one-line `Print`, 2D `PrettyPrint`, Typst via `PrintOptions::typst()`, `PrintOptions::plain()`
  (parses back).

`formalith-gui/src/`: `protocol.rs` (worker requests, cached by `line_key`), `evaluator.rs` (thread or Web
Worker backend), `geometry.rs` (CPU f64 curve sampling), `plot.rs`, `space.rs` (3D view), `shader.rs` +
`shader/*.wgsl` (implicit relations and surfaces on the GPU in f32), `typeset.rs`, `analysis.rs`, `profiler/`.

## Conventions and pitfalls

- **Adding a builtin**: append its name at the end of `Context::BUILTIN_NAMES` (ids are fixed), set its arity in
  `Context::builtin_arity` (one argument by default), and document it in `context/docs.rs` (`BUILTIN_DOCS`,
  indexed by id, with hand-written Typst results; a test checks every builtin is there).
- `SetParseExpression::MatrixArgumentSet` must never build a bigger set from a matrix set, or the parser is
  monomorphized over infinitely many types.
- **Zero tests are proofs**: decisions needing an equality use `expr::is_numerically_zero` (normalization,
  expansion, trigonometric identities), never an approximation. Signs of constants come from `constant_sign`
  (an approximation whose ball excludes 0).
- Assumptions are thread-local (`Assumptions::enter` returns a guard), installed by the parser when it has an
  `Environment`; `parse!(input, R)` without environment has none, so parallel tests don't share them.
- Results from searches (integrals, sums, ODEs) are tidied by keeping the smallest form (`expr::smallest`);
  `simplify` may not terminate on non-rational terms.
- Profiling: `profile_scope!(name)` (no-op without feature `profile`) on coarse scopes only, never in `normalize`.
- `#![allow(clippy::significant_drop_in_scrutinee)]` exists because that lint overflows clippy's stack.
- Feature `concise-debug` replaces derived `Debug` on terms with a compact form.
- Commit messages describe the behavior change with an example (`lim(...) = ...`).
