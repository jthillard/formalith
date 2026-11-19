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
`:defs` lists definitions and `:clear [name]` removes them. Systems are solved with `x + y = 3, x - y = 1`.
Assumptions on symbols are declared with `assume(a > 0, b != 0, n integer)`, giving `sqrt(a^2) = a`,
`integrate(1/a, a) = ln(a)`, `cos(2 n pi) = 1` or `lim(exp(a x), x, oo) = oo`.

## Web

`make web` builds the WebAssembly package (needs `wasm-pack`), `make web-serve` serves the page on port 8000.

## Tests

```sh
cargo test
```

CI runs `cargo fmt --all --check` and `cargo test` on pushes and pull requests. A pre-commit hook formatting the
staged Rust files is enabled with `git config core.hooksPath .githooks`.
