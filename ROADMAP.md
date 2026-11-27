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

## Soundness of numerical decisions

Places where an approximation decides an exact fact (a sign, a zero, which roots or poles exist, a branch) and can
give a wrong result rather than an unevaluated one. Examples marked *(reproduced)* give a wrong answer today.

- **`approx::approximate` has no certified error bound** (its doc says so), and everything deciding signs trusts it:
  `sign_set` in `SignMode::APPROXIMATE` (so `constant_sign`) takes any non-zero approximation as the exact sign.
  `Fixed::evaluate` gives each leaf an absolute error of about `2^-bits` and multiplies exactly, so large factors
  amplify untracked errors, and the check "enough significant bits" passes on noise. Consumers include the signs of
  radicals in Cardano's, Ferrari's and `complex_sqrt`'s roots, solutions dropped as out of range (`invert_value`,
  `ranges`), Lambert W branches, `Assumed` pruning of branches, `piecewise` conditions, `half_angle_root`, `arg`,
  CAD signs at samples, divergence signs of sums, and `rational_bound` (30 digits widened by `10^-20` without proof,
  feeding `bounds_in`, `check_bounded` and `definite::same_sign`). Known failures:
  - `Fixed::sin_cos` reduces its argument with π at the working precision, so large arguments lose every digit:
    `approx(sin(10^50))` is `0.0589…` instead of `-0.7897…`, and `piecewise(sin(10^50) > 0, 1, 0) = 1`
    *(reproduced)*. `tan` too, and only `exp` caps its argument. Reduction needs `bits + log2|x|` bits of π.
  - true zeros times large constants that normalization doesn't see as zero:
    `approx(10^40 (atan(1/2) + atan(1/3) - pi/4))` is `3.2e11` *(reproduced)*.
  - discontinuous builtins (`floor`, `ceil`, `sign`, `min`, `max`) are evaluated on approximated arguments, so
    `piecewise(floor(4 (atan(1/2) + atan(1/3))/pi) = 1, 1, 0) = 0` *(reproduced)*; an argument near a jump should
    give no value.

  Interval (ball) arithmetic in `Fixed`, a running error bound per node, would make every consumer sound at once.
- **`R::reduce_angle`** (`atan(tan θ) = θ - kπ`, also `eval_atan_half_angle`) takes `k` from a 96-bit
  approximation of `θ/π` with a fixed `2^-32` margin, while the error grows with `|θ|`: `atan(tan(10^30))` and
  `atan(tan(10^32))` are off by `13π` and `1277π`, outside `(-π/2, π/2)` *(reproduced)*.
- **Limits.**
  - `gruntz::is_zero` takes a constant approximating 0 as zero. It takes a coefficient in `x` as zero when it is 0
    at every test point where it can be evaluated, and one such point is enough. The test points lie in
    `(0, 7.2]`, so `(9x - 64) ln(x - 7)` is "zero" (defined only at `64/9` there), and
    `lim(x - exp(x) (9x - 64) ln(x - 7), x, oo)` is `+oo` instead of `-oo` *(reproduced; `63` gives `-oo`)*.
    Points should be spread over the domain, at least two evaluable points should be needed, and non-zero should
    be the default.
  - `without_angles` keeps a result as independent of the angles when its samples agree within `10^-18` and
    their difference has no approximate sign, so `lim(sin(10^(-2000) sin(x)), x, oo)` is 0 instead of
    `undefined` *(reproduced)*.
- **Definite integrals.**
  - `periodic_zeros` lists the poles of `tan` and the zeros of `sin` / `cos` in denominators from `floor` / `ceil`
    in f64 without widening, and only candidates are checked exactly, so a pole near a bound is missed:
    `integrate(tan(3x), x, 7, 5pi/2 + 10^(-40))` is finite *(reproduced)*.
  - `compare_points` takes two points close in f64 whose difference has no approximate sign (below about
    `2^-4560`, or not approximable) as equal, so `sort_points` / `dedup` can merge a pole into a bound and `abs.rs`
    pieces can be lost.
  - `interior` ignores points within `10^-12` of a bound with no exact check, so `constant_parts`
    (`atan(1/(x - 10^-13)) + atan(x - 10^-13)` taken as constant on `[0, 1]`), `square_root` and `range_sign`
    can be wrong near the bounds.
  - `nicer_value` prefers the substituted value when it agrees with the limit within `2^-48`, and
    `C::principal_parts` checks bases with unwidened 30-digit bounds.
- **Inequalities (CAD).**
  - `eliminated_roots` keeps the roots of the resultant where the lifted polynomial is within `10^-30` of 0. The
    bound is absolute and not scaled by the coefficients or the root, so true roots of polynomials with large
    coefficients are dropped and close conjugate roots can pass.
  - `rational_value`, `Root::same` and `same_bound` / `merge` take "indistinguishable at the maximum precision",
    a failed approximation (`None`), or a relative `10^-30` as equality.
- **Optimization.** `optimize::compare` trusts a 64-bit approximation of the difference once it is above
  `2^-32`, though the error is multiplied by the size of the terms (`exp(50) (sqrt(2) - r)`), and so does
  `keep_lowest`.
- **Sums.** `zeilberger::negligible` takes `constant_sign(..) == None` as agreement between the closed form and
  the sum below `n_0`, so a closed form that can't be approximated there (a pole, `undefined`) loses its
  exceptional case. `ratfun::natural_roots` silently skips candidates above `MAX_ROOT` rather than failing, which
  can make `n_0` too small.
- **Solving.** `inverse/exponential.rs` sorts the rates by their f64 value (`Numeric`) and computes their exact
  signs without using them. A badly rounded rate can reorder them, undercounting the sign changes `N`, and then
  `N` exact roots are taken as all of them. Sorting by `constant_sign` of differences would avoid it.

Checked and sound, since approximations there only reject or are checked exactly: the Risch structure theorems
(`risch/tower.rs`, exact over ℚ), RDE candidates, Gosper shifts, `consistent_at_sample`, `verify_by_ode` (numbers
only reject, proofs are exact) and guessed recurrences (`Recurrence::proves`), candidate roots of exponential sums
(`vanishes_at`), `sample_between`, `same_sign` (exact rational intervals, up to `rational_bound`), Hessian minors
(an undecided one falls back to the CAD), `list_periodic` and `ranges::round`.

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
