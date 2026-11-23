# Roadmap

Ideas and known gaps, roughly by area. `AGENTS.md` describes what exists; this file lists what doesn't yet.

## Series

- **Algebraic functions in the holonomic engine.** Every algebraic function is D-finite: from its polynomial
  `P(x, f) = 0`, reduce the derivatives of `f` modulo `P` and find a linear dependency. `sqrt(1 + sqrt(1 + x))`
  (`f^4 - 2 f^2 - x = 0`) and other nested radicals would then be proven by their recurrence. Today they reach
  the fallback, whose zero test fails.
- **Algebraic zero test for the verified fallback.** Replace each radical by a symbol with its defining relation
  (`u^2 = 1 + x`, `v^2 = 1 + u`), then reduce the numerator level by level. A zero remainder proves the identity;
  a non-zero one only makes the test inconclusive. `simplify` treats radicals as independent and is too slow
  above about 80 nodes.
- **Petkovšek's *Hyper*** for recurrences without a two-term form, with exact arithmetic over algebraic numbers.
  Today only rational functions with simple real poles are handled, by partial fractions.
- **Real forms for complex poles.** `1/(1 - x + 2 x^2)` could give `r^k cos(k θ)` / `sin(k θ)` terms, like
  `dsolve` does for complex characteristic roots. Multiple irrational poles are unsupported too.
- **`series(f, x, a, oo)` in `C`**, through the real and imaginary parts like finite series.
- **Known non-holonomic series**: `tan`, `sec`, `x / (e^x - 1)` with Bernoulli or Euler numbers
  (`special::bernoulli`).
- **Held sums**:
  - derivatives and integrals term by term, so that `diff(series(...), x)` evaluates;
  - partial sums for `approx` and for graphs (`Numeric` doesn't support them);
  - printing `4^k` rather than `2^(2k)`.
- `exp(a ln u)` with a symbolic `a` is slow in the series engine: `series((1 + x)^a, x, 0, 8)` doesn't finish.

## Approximation

- `approx` underflows to `0.0` below about `1e-1385` (`approx(1/factorial(700))`): the fixed-point precision
  should follow the magnitude of the result.
- `gamma` and `polygamma` of very large arguments are slow (`approx(gamma(10^6 + 1/3))` takes minutes in a
  debug build).

## Complex numbers

- `approx`, `re` and `im` don't evaluate transcendental values in `C` (`approx(exp(1 + i))`, `re(exp(i))`).

## Limits

- `gamma(g)` with `g -> -oo`.

## Integration

- The algebraic case of the Risch algorithm: roots in the tower.
- Irrational residues above `QQ(x)` in Rothstein-Trager.
- `Ci` only for positive arguments.

## Solving

- Cyclotomic polynomials whose roots aren't classic radicals (`Φ_7`).
- The `W_-1` branch of `lambertw`.
- The polynomial solver hangs on `x + sqrt(x)` (worked around by `solve/inverse.rs`).
- `Term::factor` hangs over `Z`.

## Inequalities and optimization

- Inequalities: parameters, more than 3 unknowns or 40 polynomials.
- `argmin` / `argmax`:
  - periodic special points, `floor`, `ceil` and `piecewise`;
  - several variables beyond rational functions without parameters;
  - extrema of two variables whose values come from Cardano's formula are slow.

## Sums

- `simplify` may not terminate on non-rational results (`sum::tidy` avoids it).

## Differential equations

- Higher orders with non-constant coefficients. The holonomic engine could give their power series solutions.
- Constant solutions of separable equations aren't listed.
- Implicit solutions only take `y(a) = b` conditions.

## Matrices

- Eigenvalues when the characteristic polynomial has non-real roots (currently unevaluated), and matrices over
  `C`.
- `simplify`, `expand` and `diff` of matrix literals don't parse in `M` (`simplify([[x, 1], [0, x]])`).

## Other sets

- `N` has no arithmetic and its normalization is `todo!()`: `integrate(x, x)` in `N` panics (caught by sessions)
  instead of returning an error.

## GUI

- Remarkable points (roots, extrema) on WebGL2, which has no compute shaders.
- Hover labels and analysis for complex maps.

## Tooling

- `cargo clippy` hangs on the crate's recursive types.
- `cargo llvm-cov` doesn't find the objects in the nightly build directory layout
  (`target/llvm-cov-target/debug/build/<crate>/<hash>/out/`); coverage needs merging the profiles with the
  toolchain's `llvm-profdata` and calling `llvm-cov report` on the test binaries by hand.
- Self-checks not written yet: random identities of `gamma` / `polygamma` (reflection, duplication, recurrence),
  sums with a symbolic upper bound checked at several `n`, integrals with symbolic bounds checked by
  substitution, random constant-coefficient ODEs with conditions (`check_gamma`, `check_sum`, `check_integrate`,
  `check_dsolve`).
- Ignored tests for future work: definite integrals without elementary antiderivatives (Dirichlet, `ln(sin)`,
  `tests/integrate.rs`) and numerical integration of oscillating integrands on infinite intervals
  (`tests/approx.rs`).
