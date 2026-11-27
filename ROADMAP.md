# Roadmap

Known gaps and ideas, by area. `AGENTS.md` describes the code; this file lists what doesn't work yet. Examples
are checked with `cargo run --release -- '<input>'`.

## Solving

- **`nsolve`** for equations without closed form, explicitly numerical: bracketing and refinement in `approx`'s
  fixed-point arithmetic, like `rootof` for polynomials (`polynom/real_roots.rs`). Targets: `cos(x) = x`,
  kernels mixed with polynomial parts (`x + sin(x) = 1`, `x sin(x) = 1`), exponential sums with irrational roots
  (`2^x + 3^x = 7`).
- **Non-real `rootof`**: polynomials without radical roots in `C` (`x^5 = 2` can't be solved there), and
  polynomials with irrational or symbolic coefficients (`x^5 + sqrt(2) x + 1 = 0`).
- `rootof` arithmetic only reduces powers of a single root: sums and products of different roots aren't
  simplified, and denominators like `1/(α + 1)` aren't rationalized.
- Unrelated angles beyond `a sin u ± a sin v`: `tan` (`tan(x) = tan(x^2)`, whose excluded points `cos = 0` would
  have to be removed from whole families) and coefficients of different sizes (`sin(x) = 2 cos(x^2)`).
- Trigonometric polynomials with irrational or symbolic coefficients (`sin(3x) + cos(x) = sqrt(2)`).
- Ranges of integer parameters are only found for conditions affine in a single parameter; others
  (`sqrt(k^2 - 2)`, nested parameters) leave the solution unchecked.

## Simplification

- Radical towers above dimension 64 (`1/(1 + 6^(1/64) + sqrt(5))`), nested roots of sums that aren't positive,
  and zero divisors of their tower (a reducible `y^q - b`) stay unrationalized; products of nested radical sums
  aren't expanded (it made Ferrari's roots too slow).
- Roots of different orders aren't merged: `72^(1/6) - sqrt(2)*3^(1/3)` isn't 0.
- Trigonometric forms with several unrelated constant angles keep nested forms; `simplify` only linearizes
  products of at most 8 `sin` / `cos` factors.

## Soundness of numerical decisions

Signs come from balls whose radius bounds the error, and zero tests are proofs (`expr::is_numerically_zero`).
What is left:

- Zeros these proofs don't see stay undecided: nested radicals equal to a rational their tower doesn't reach,
  polynomials in `cos(a)` of an angle whose multiple isn't a classic value. Zero tests in the tower of the
  constant's algebraic numbers (`cos(2π/9)` as a root of its minimal polynomial) would recover more.
- Numerical integration, tails of held sums, the Gamma family, `zeta`, Lambert W, `erf`, `erfi`, `Si`, `Ci` and
  `Ei` estimate their errors rather than bound them.
- `approx` loses values below about `2^-4360` coming from absolute-precision operations (`approx(sin(10^-2000))`
  is `0.0`): the fixed-point precision should follow the magnitude of each intermediate value.

## Assumptions

- Case splits of calculus builtins (`real/cases.rs`) only split at rational points of a single parameter, not at
  points depending on other parameters (`a = b`). Inner integrals are normalized, and split on the outer
  variable, before the outer integral assumes its range.
- Definite integrals with symbolic bounds assume `a < x < b` only for bounds linear in symbols.
- Integrality only rounds bounds of single symbols: `assume(m integer, n integer, n < m, m < n + 1)` is accepted.
- Nonlinear assumptions (`a b > 1`) and assumptions with builtin constants (`a > pi`) are rejected.
- Fourier-Motzkin elimination gives up past 400 constraints, taking the system as feasible (sound, but nothing is
  concluded).

## Series

- Relations between radical bases that aren't common factors over ℚ (nested radicals with related bases), bases
  vanishing at the point, and towers above dimension 64.
- Series at `-oo` of the Gamma family aren't reflected like limits (`series(gamma(x)*sin(pi*x), x, -oo, 3)`).
- Petkovšek's *Hyper* over algebraic numbers (ratios other than rational or Gaussian, factors with irrational
  roots), with parameters, and coefficients without hypergeometric solutions (`series(x exp(x^2) cos(x), x, 0, oo)`
  would need d'Alembertian or Liouvillian solutions).
- Rational functions with several pairs of complex roots without radicals, or with symbolic or irrational
  coefficients.
- Known non-holonomic series: hyperbolic kernels and `1/(e^t - 1)` at regular points other than 0, products of
  two kernels (`series(tan(x)/cos(x), x, 0, oo)`).
- Held sums: definite integrals on the boundary of the disk of convergence
  (`integrate(series(1/(1 + x), x, 0, oo), x, 0, 1)`, Abel's theorem) and on infinite intervals; on the GPU they
  are summed in f32, so terms overflowing it (`x^k` with a large `x`, `(2k)!`, Bernoulli numbers beyond `B_64`)
  give NaN where the CPU still sums them.

## Integration

- The algebraic case of the Risch algorithm (roots in the tower).
- Rothstein-Trager residues at roots of irreducible factors of degree 3 or more above `QQ(x)`.
- Definite integrals without elementary antiderivatives beyond Dirichlet's and Mellin-type ones:
  `integrate(ln(sin(x)), x, 0, pi)`, `integrate(ln(x)/(1 + x^2), x, 0, oo) = 0`, `integrate(sin(x)^2/x^2, x, 0, oo)`
  (ignored test in `tests/integrate.rs`); numerical integration of oscillating integrands on infinite intervals
  (ignored test in `tests/approx.rs`).

## Sums

- Zeilberger's algorithm beyond order 2 (the certificate over `QQ(n)` blows up), inhomogeneous recurrences of
  order 2, *Hyper* with parameters, lower bounds depending on `n`, infinite upper bounds, and boundary terms like
  `binomial(n, 2n)` (zero only for `n >= 1`), so `sum(binomial(n, 2k), k, 0, n)` stays unevaluated.
- Gosper's antidifferences with symbolic bounds give generic values without the cases Zeilberger's results get.
- `simplify` may not terminate on non-rational results (`sum::tidy` avoids it).

## Differential equations

- Linear equations with non-constant coefficients beyond homogeneous ones at an ordinary point: regular singular
  points (Frobenius series, Bessel's `x^2 y'' + x y' + (x^2 - 1) y = 0`), closed forms instead of series
  (Cauchy-Euler `x^2 y'' + x y' - y = 0`), inhomogeneous equations, and solutions without a two-term or
  hypergeometric recurrence (`y'' + (1 + x) y = 0`). General terms of period 2 or more aren't reduced.
- Nonlinear equations of order 2 or more (reduction of order for `y'' = f(y, y')`).

## Inequalities and optimization

- Inequalities with parameters, more than 3 unknowns or 40 polynomials, or functions other than `abs` and roots
  (`exp`, `log`, trigonometric functions, `min` / `max`).
- `argmin` / `argmax`: periodic special points, `floor`, `ceil` and `piecewise`; several variables beyond rational
  functions without parameters; extrema of two variables whose values come from Cardano's formula are slow.

## Sequences

Sequences of `R^N` and `C^N` are closed forms or systems of recurrences (`field/commons/sequence/`), with terms,
shifts and componentwise operations. Recursive definitions (`u(0) := 1`, `u(n) := 2 u(n - 1) + 1`) give them in
sessions, and their terms in `R`, `C` and `Z`.

- Limits, convergence, boundedness and monotonicity of sequences (`lim(u)` over integers, `lim((-1)^n / n) = 0`,
  `lim((-1)^n)` undefined). `lim`, `sum`, `integrate`... of a closed form are its general term's, componentwise.
- Closed forms of recurrences (`rsolve`): constant coefficients (Binet), first order, hypergeometric solutions
  with *Hyper* (`holonomic/hyper.rs`).
- Equality and zero tests are structural (canonical systems, expansion of the rules): a canonical P-recursive
  form with the Ore closure (`holonomic/ore.rs`, `lclm`, `symmetric_product`) would decide them for linear
  recurrences (`fib(n + 1)^2 - fib(n) fib(n + 2) = (-1)^n` stays a system).
- Partial sums `sum(u(k), k, 0, n)` and series of recurrences, generating functions.
- Sets `Z^N`, `N^N`, `(Z/n)^N`; terms of recursive definitions in `Z/n` and `N` stay unevaluated.
- Self-references other than `u(n - d)` (`u(n/2)`, `u(n + 1)`), mutually recursive sequences, subsequences `u(2n)`
  of recurrences, sequences of several indices (`c(n, k)`).
- Shifts by more than 256, or whose rule grows beyond 200 nodes (nonlinear recurrences), shift the starts of the
  system rather than its rules, so they don't simplify with the original sequence.
- `piecewise` in recursive rules: every branch is computed, so a rule `piecewise(n < 0, 0, u(n - 1))` needs its
  initial values.
- Calls with a symbolic argument (`sum(u(k), k, 1, 10)` in `R`) stay unevaluated, definitions being expanded when
  parsed.
- Sequences of `C^N` in the GUI (points of their real and imaginary parts); the terms of recurrences are
  recomputed in f64 for each frame.

## Matrices

- Eigenvalues in the trigonometric form of Cardano's or Ferrari's roots (characteristic polynomials
  `x^3 - 3x - 1`, `x^4 + x + 1`) stay unevaluated: expansion can't prove `p(λ) = 0` (`cos(acos(c)/3)`), so
  multiplicities and eigenspaces aren't found. Reducing modulo the minimal polynomial of `λ` would. Cubics and
  quartics with non-rational coefficients aren't solved.

## GUI

- Implicit relations and regions are evaluated in f32 on the GPU, so they lose precision when zoomed in deep.
- Hover labels and analysis for complex maps.

## Tooling

- `cargo llvm-cov` doesn't find the objects in the nightly build directory layout; coverage needs merging the
  profiles with the toolchain's `llvm-profdata` and calling `llvm-cov report` on the test binaries by hand.
- Self-check of integrals with symbolic bounds by substitution (`check_integrate` only checks antiderivatives and
  numeric bounds).
