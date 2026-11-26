# Roadmap

Ideas and known gaps, roughly by area. `AGENTS.md` describes what exists; this file lists what doesn't yet.

## Series

- **Relations between radical bases** that aren't common factors over ℚ: nested radicals with related bases
  (`sqrt(1 + sqrt(1 + x))` next to `sqrt(2 + 2 sqrt(1 + x))`), bases vanishing at the point, and towers above
  dimension 64.
- **Petkovšek's *Hyper*** over algebraic numbers: ratios `Z` other than rational or Gaussian, factors `A` and `B`
  with irrational roots, and recurrences with parameters; non-hypergeometric coefficients (`x e^(x^2) cos x`, whose
  recurrence has no hypergeometric solution) would need d'Alembertian or Liouvillian solutions.
- **More poles of rational functions**: irreducible factors of degree 4 or more with several pairs of complex roots
  that `C` doesn't find (`1/(1 + x + x^5)` has two pairs), and rational functions with symbolic or irrational
  coefficients.
- **Known non-holonomic series**: hyperbolic kernels and `1/(e^t - 1)` at regular points other than 0 (their poles
  are complex), products of two kernels (`tan(x) / cos(x)`).
- **Held sums**:
  - definite integrals on the boundary of the disk of convergence (`integrate(series(1/(1 + x), x, 0, oo), x, 0, 1)`,
    Abel's theorem) and on infinite intervals;
  - partial sums on the GPU are in f32, so general terms overflowing it (`x^k` with a large `x`, `(2k)!`, Bernoulli
    numbers beyond `B_64`) give NaN where the CPU still sums them.

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

- Radical towers above dimension 64 (`1/(1 + 6^(1/64) + sqrt(5))`), nested roots of sums that aren't positive, and
  sums that are zero divisors of their tower (a reducible `y^q - b`) stay unrationalized; products of nested radical
  sums aren't expanded (expanding them made Ferrari's roots too slow).
- Constant radicals aren't fully canonical across inputs: roots of different orders aren't merged
  (`72^(1/6)` vs `sqrt(2) 3^(1/3)`).
- Trigonometric forms with several unrelated constant angles keep nested forms; `simplify` only linearizes products
  of at most 8 `sin` / `cos` factors.

## Assumptions

- Case splits of calculus builtins (`real/cases.rs`) only split at rational points of a single parameter, not at
  points depending on other parameters (`a = b`). Inner integrals are normalized, and split on the outer variable,
  before the outer integral assumes its range.
- Definite integrals with symbolic bounds assume `a < x < b` only for bounds linear in symbols.
- Integrality only rounds bounds of single symbols: relations between several integers are decided over ℚ, so
  `assume(m integer, n integer, n < m, m < n + 1)` isn't a contradiction.
- Nonlinear assumptions (`a b > 1`, `a^2 < 2`) and assumptions with builtin constants (`a > pi`) are rejected.
- Fourier-Motzkin elimination gives up past 400 constraints, taking the system as feasible (sound, but nothing is
  concluded).

## Approximation

- `approx` keeps tiny values whose evaluation has their relative precision (exact ones, `exp` of negative
  arguments, roots, `W_-1`, products and quotients of them), but values below about `2^-4360` coming from
  absolute-precision operations (deep cancellations, `sin(10^-2000)`, `atan` of tiny arguments) are still `0.0`:
  the fixed-point precision should follow the magnitude of each intermediate value.

## Limits

- `polygamma(m, g)` with `g -> -oo` (reflection with derivatives of `cot`), and `gamma` at `-oo` nested in
  internal limits.

## Integration

- The algebraic case of the Risch algorithm: roots in the tower.
- Rothstein-Trager residues at the roots of irreducible factors of degree 3 or more above `QQ(x)` (quadratic ones
  are done).

## Inequalities and optimization

- Inequalities: parameters, more than 3 unknowns or 40 polynomials.
- `argmin` / `argmax`:
  - periodic special points, `floor`, `ceil` and `piecewise`;
  - several variables beyond rational functions without parameters;
  - extrema of two variables whose values come from Cardano's formula are slow.

## Sums

- **Zeilberger's algorithm** beyond order 2 (evaluating the certificate over `QQ(n)` blows up), inhomogeneous
  recurrences of order 2, *Hyper* with parameters, lower bounds depending on `n` and infinite upper bounds, and
  boundary terms like `binomial(n, 2n)` (zero only for `n >= 1`), so `sum(binomial(n, 2k), k, 0, n)` stays
  unevaluated. Gosper's antidifferences with symbolic bounds give generic values
  (`sum((-1)^k (k + 2) binomial(n, k), k, 0, n) = 0`, wrong at `n = 1`), without the cases Zeilberger's results get.
- `simplify` may not terminate on non-rational results (`sum::tidy` avoids it).

## Differential equations

- Linear equations with non-constant coefficients beyond homogeneous ones with rational coefficients at an
  ordinary point: regular singular points (Frobenius series, Bessel's equation `x^2 y'' + x y' + (x^2 - 1) y = 0`),
  closed forms instead of series (Cauchy-Euler `x^2 y'' + x y' - y = 0`), inhomogeneous equations, and solutions
  whose coefficients have no two-term or hypergeometric recurrence (`y'' + (1 + x) y = 0`, Airy's equation at
  `x0 = 1`). General terms of period 2 or more aren't reduced (`-4 (k + 1)/(16 k^2 - 4)` for Legendre's equation).
- Nonlinear equations of order 2 or more (reduction of order for `y'' = f(y, y')`).

## Matrices

- Eigenvalues in the trigonometric form of Cardano's or Ferrari's roots (cubics with three real roots, quartics like
  `x^4 + x + 1` in `C`) stay unevaluated in `M` and `M(C)`: expansion can't prove `p(λ) = 0`
  (`cos(acos(c)/3)`), so multiplicities and eigenspaces aren't found. Reducing modulo the minimal polynomial of
  `λ` would. Cubics and quartics with non-rational coefficients (Gaussian ones in `M(C)`) aren't solved.

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
