# Roadmap

Ideas and known gaps, roughly by area. `AGENTS.md` describes what exists; this file lists what doesn't yet.

## Series

- **Relations between radical bases.** The tower of `holonomic/algebraic.rs` has one independent generator per
  base, so proportional or otherwise related bases (`sqrt(2 + 2x)` next to `sqrt(1 + x)`, `sqrt(x^2 + 2x + 1)`)
  only make its zero test inconclusive, and towers above dimension 16 are rejected.
- **Petkovšek's *Hyper*** for recurrences without a two-term form, with exact arithmetic over algebraic numbers.
  Today only rational functions with simple poles, real or roots of quadratic factors, are handled, by partial
  fractions.
- **More poles of rational functions**: multiple irrational poles, complex roots of irreducible factors of degree 3
  or more (`1/(1 + x + x^3)`).
- **`series(f, x, a, oo)` in `C`**, through the real and imaginary parts like finite series.
- **Known non-holonomic series** beyond a kernel with Bernoulli or Euler numbers times a power of `x`:
  `tan(x)^2`, `tan(x) / (1 + x)`, `tan(x)` at 1.
- **Held sums**:
  - definite integrals term by term, and integrals of terms that aren't a power of a linear term;
  - `approx` of a held sum equal to zero raises the precision to its maximum, which is slow (seconds);
  - partial sums on the GPU (`Numeric::Sum` is NaN there).
- `exp(a ln u)` with a symbolic `a` is slow in the series engine: `series((1 + x)^a, x, 0, 8)` doesn't finish.

## Solving

- **`nsolve`** for equations without closed form (`cos(x) = x`), explicitly numerical: bracketing and refinement in
  `approx`'s fixed-point arithmetic, like `rootof` does for polynomials (`polynom/real_roots.rs`).
- **Non-real `rootof`**: polynomials without radical roots in `C` (`x^5 = 2` is "can't solve" there), and
  polynomials with irrational or symbolic coefficients (`x^5 + sqrt(2) x + 1`).
- `rootof` arithmetic only reduces powers of a single root: sums and products of different roots aren't simplified,
  and denominators like `1/(α + 1)` aren't rationalized.
- **Transcendental equations** without closed form, for `nsolve`: kernels mixed with polynomial parts
  (`x + sin(x) = 1`, `x sin(x) = 1`) and exponential sums with irrational roots (`2^x + 3^x = 7`).
- Unrelated angles beyond `a sin u ± a sin v`: `tan` (`tan(x) = tan(x^2)`, whose excluded points `cos = 0` would
  have to be removed from whole families), coefficients of different sizes (`sin(x) = 2 cos(x^2)`).
- Ranges of integer parameters are only found for conditions affine in a single parameter; others (`sqrt(k^2 - 2)`,
  nested parameters) leave the solution unchecked. Trigonometric polynomials with irrational or symbolic
  coefficients still need radicals (`sin(3x) + cos(x) = sqrt(2)`).

## Simplification

- **Rationalizing denominators** mixing radicals of different orders and bases (`1/(√2 + ∛3)`), with nested
  radicals (`1/(1 + √(2 + √2))`) or in `C`.
- Trigonometric solutions with several angles or no half-angle form keep nested forms, like
  `asin(1/√(sin(1)² + 2 cos(1) + cos(1)² + 1))` (`sin² + cos² = 1` isn't applied there).

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
