# Formalith

A computer algebra system written in Rust. Expressions are generic over the algebraic structure they live in
(a set, group, ring or field), so the same expression can be evaluated over different sets.

## Sets

- `N`: natural integers (ordering only)
- `Z`: integers
- `R`: reals, with exact rationals and symbolic constants (`pi`, `e`)
- `C`: complex numbers over Gaussian rationals (`i` is the imaginary unit)
- `Z/n`: integers modulo `n`
- `K[x]`: univariate polynomials over a set `K`
- `M`: matrices with symbolic entries

`R` supports derivatives, limits, series, integrals (with the Risch algorithm), sums and products (with Gosper's
algorithm, `sum(k^2, k, 1, n)`, `sum(1/k^2, k, 1, oo)`, `product(k, k, 1, n)`), numerical approximations,
factorization, solving systems of polynomial equations and ordinary differential equations (`dsolve(y' = x*y)`,
`dsolve(y'' + y = 0, y(0) = 1, y'(0) = 0)`: separable, first-order linear, and linear with constant coefficients).

## Crates

- `crates/formalith`: the computer algebra system library
- `crates/formalith-session`: interactive sessions (commands, definitions, results), shared by the interfaces
- `crates/formalith-cli`: the command line interface (binary `formalith`)
- `crates/formalith-web`: the browser interface (WebAssembly)
- `crates/formalith-gui`: a graphing calculator (egui), natively and in the browser

## Library

Nightly Rust is required (`rust-toolchain.toml` pins it).

```rust
use formalith::{field::real::R, parse};

let f = parse!("(x^2 - 1)/(x - 1)", R);
println!("{}", f.simplify());
println!("{}", parse!("integrate(x e^x, x)", R));
println!("{}", parse!("lim(sin(x)/x, x, 0)", R));
```

## Command line

```sh
cargo run                                # interactive REPL in R
cargo run -- 'diff(sin(x)^2, x)'         # evaluate arguments
cargo run -- --set 'Z/7' 'factor(x^2 + 1)'
```

In the REPL, `:set <name>` changes the set, `:typst` toggles Typst output, `f(x) := x^2` defines a function,
`:defs` lists definitions and `:clear [name]` removes them, `help builtins` lists the builtin functions and
`help <name>` documents one. Systems are solved with `x + y = 3, x - y = 1`.
Assumptions on symbols are declared with `assume(a > 0, b != 0, n integer)`, giving `sqrt(a^2) = a`,
`integrate(1/a, a) = ln(a)`, `cos(2 n pi) = 1` or `lim(exp(a x), x, oo) = oo`. Sessions start with `k`, `m` and
`n` assumed integer: `:assumptions` lists every assumption, defaults included, `:clear n` drops one and `:clear`
restores the defaults.

## Web

`./dev web` builds the WebAssembly package (needs `wasm-pack`), `./dev web --serve` also serves the page on port 8000.
Add `--release` for an optimized build (otherwise a debug build without `wasm-opt`), see `./dev --help`.
`./dev docs --serve` writes the documentation page of the builtins into `target/docs-site/` and serves it on port
8002.

## Graphing calculator

`./dev gui` runs the graphical interface (`cargo run -p formalith-gui`): a list of lines with their results, next
to a plot of curves (`y = sin(x)`, `f(x) := x^3 - x`, `x = y^2`), implicit curves and regions (`x^2 + y^2 = 1`,
`y < exp(-x^2)`) and points (`(1, f(1))`), with sliders for parameters (`y = a*sin(b*x)`) and the roots, extrema
and intersections of the selected curve. `./dev gui-web` builds it for the browser (WebGPU, or WebGL2 without it),
`./dev gui-web --serve` also serves it on port 8001.

## Tests

```sh
cargo test --workspace
```

The files `crates/formalith/tests/check_*.rs` check results against their definition rather than against
hand-written outputs (derivatives of antiderivatives, substituted solutions, sampled regions and extrema, partial
sums, `approx` against floating point...). Their random fuzzers are ignored by default:

```sh
cargo test --release -p formalith -- --ignored fuzz
FORMALITH_FUZZ_CASES=500 FORMALITH_SEED=42 cargo test -p formalith --test integration check_optimize:: -- --ignored
```

A failure prints the seed and the failing inputs. `FORMALITH_SHOW_SKIPPED=1` lists skipped cases,
`FORMALITH_TIMES=1` prints the time of each case and `FORMALITH_WORKERS` sets the number of threads.

CI runs `cargo fmt --all --check` and `cargo test --workspace` on pushes and pull requests. A pre-commit hook formatting the
staged Rust files and running `cargo clippy --workspace --all-targets` (failing on warnings) is enabled with
`git config core.hooksPath .githooks`. The fuzzers run every night with a new seed
(`.github/workflows/fuzz.yml`, also started by hand with a number of cases and a seed).
