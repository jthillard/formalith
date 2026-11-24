# Roadmap

Ideas and known gaps, roughly by area. `AGENTS.md` describes what exists; this file lists what doesn't yet.

## Series

- **Relations between radical bases.** The tower of `holonomic/algebraic.rs` has one independent generator per
  base, so proportional or otherwise related bases (`sqrt(2 + 2x)` next to `sqrt(1 + x)`, `sqrt(x^2 + 2x + 1)`)
  only make its zero test inconclusive, and towers above dimension 16 are rejected.
- **Petkovšek's *Hyper*** for recurrences without a two-term form, with exact arithmetic over algebraic numbers.
  Today only rational functions with simple real poles are handled, by partial fractions.
- **Real forms for complex poles.** `1/(1 - x + 2 x^2)` could give `r^k cos(k θ)` / `sin(k θ)` terms, like
  `dsolve` does for complex characteristic roots. Multiple irrational poles are unsupported too.
- **`series(f, x, a, oo)` in `C`**, through the real and imaginary parts like finite series.
- **Known non-holonomic series**: `tan`, `sec`, `x / (e^x - 1)` with Bernoulli or Euler numbers
  (`special::bernoulli`).
- **Held sums**:
  - derivatives and integrals term by term, so that `diff(series(...), x)` evaluates;
  - partial sums for `approx` and for graphs (`Numeric` doesn't support them).
- `exp(a ln u)` with a symbolic `a` is slow in the series engine: `series((1 + x)^a, x, 0, 8)` doesn't finish.

## Solving

- **Polynomials without radical roots** (`x^5 - x - 1 = 0` is "can't solve"): real roots isolated by Sturm
  sequences or Descartes' rule, refined with `approx`'s fixed-point arithmetic, as numerical roots or a `RootOf`-like
  value. An `nsolve` builtin for other equations (`cos(x) = x`) could share it, and the inequality CAD and `argmin`
  could use it where radicals stall.
- **Transcendental equations** still unsupported: kernels mixed with polynomial parts (`x + sin(x) = 1`,
  `x sin(x) = 1`), trigonometric functions of unrelated angles (`sin(x) = cos(x^2)`), more than two exponential
  terms of different bases (`2^x + 3^x = 5`), and trigonometric polynomials whose degree is too high for radicals
  (`sin(3x) + cos(x) = c` gives a sextic in `tan(x/2)`).

## Simplification

- **Rationalizing denominators** with radicals: `tan(pi/12)` is `(√6 - √2)/(√6 + √2)` rather than `2 - √3`, and
  solutions of trigonometric equations keep forms like `atan(1/cos(1) + sin(1)/cos(1))`.

## Approximation

- `approx` underflows to `0.0` below about `1e-1385` (`approx(1/factorial(700))`): the fixed-point precision
  should follow the magnitude of the result. `exp` of negative arguments and `W_-1` keep their relative precision,
  but other tiny intermediate values (small powers, differences) still lose it.
- `gamma` and `polygamma` of very large arguments are slow (`approx(gamma(10^6 + 1/3))` takes minutes in a
  debug build).

## Limits

- `polygamma(m, g)` with `g -> -oo` (reflection with derivatives of `cot`), and `gamma` at `-oo` nested in
  internal limits.

## Integration

- The algebraic case of the Risch algorithm: roots in the tower.
- Irrational residues above `QQ(x)` in Rothstein-Trager.
- `Ci` only for positive arguments.

## Inequalities and optimization

- Inequalities: parameters, more than 3 unknowns or 40 polynomials.
- `argmin` / `argmax`:
  - periodic special points, `floor`, `ceil` and `piecewise`;
  - several variables beyond rational functions without parameters;
  - extrema of two variables whose values come from Cardano's formula are slow.

## Sums

- **Zeilberger's algorithm** (creative telescoping) for definite hypergeometric sums, which Gosper's algorithm
  can't do: `sum(binomial(n, k), k, 0, n)`, `sum(k binomial(n, k), k, 0, n)` and `sum(binomial(n, k)^2, k, 0, n)`
  stay unevaluated. Its recurrences would be solved by *Hyper* (see Series), and the parts exist: `gosper.rs`, the
  parameter fractions `QQ(t)` and `solve_linear`.
- `simplify` may not terminate on non-rational results (`sum::tidy` avoids it).

## Differential equations

- Higher orders with non-constant coefficients, like the Airy equation `y'' + x y = 0`. The holonomic engine
  could give their power series solutions.
- Implicit solutions only take `y(a) = b` conditions.

## Matrices

- Eigenvalues when the characteristic polynomial has non-real roots (`eigenvalues([[0, -1], [1, 0]])` is
  unevaluated, though `C` and `split_complex` exist), and matrices over `C`.
- `simplify`, `expand` and `diff` of matrix literals don't parse in `M` (`simplify([[x, 1], [0, x]])`).

## GUI

- Implicit relations and regions are evaluated in f32 on the GPU, so they lose precision when zoomed in deep (curves
  are sampled in f64 on the CPU).
- Hover labels and analysis for complex maps.

## Tooling

- `cargo clippy` hangs on the crate's recursive types.
- `cargo llvm-cov` doesn't find the objects in the nightly build directory layout
  (`target/llvm-cov-target/debug/build/<crate>/<hash>/out/`); coverage needs merging the profiles with the
  toolchain's `llvm-profdata` and calling `llvm-cov report` on the test binaries by hand.
- Self-check not written yet: integrals with symbolic bounds checked by substitution (`check_integrate` only
  checks antiderivatives and numeric bounds).
- Ignored tests for future work: definite integrals without elementary antiderivatives (Dirichlet, `ln(sin)`,
  `integrate(ln(x)/(1 + x^2), x, 0, oo) = 0`, `tests/integrate.rs`) and numerical integration of oscillating
  integrands on infinite intervals (`tests/approx.rs`).
