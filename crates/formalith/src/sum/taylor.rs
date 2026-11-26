//! Whole series `series(f, x, a, oo)`: the general term of the Taylor (Laurent, Puiseux) series of `f`.
//!
//! The coefficients `{$c_0, ..., c_N$}` of the series in `w` are computed exactly, then a recurrence
//! `{$P(n) c_(n + m) = Q(n) c_n$}` is guessed, with polynomials `P` and `Q` and a period `m`, and proven:
//! - for holonomic functions (see [`holonomic`]), the coefficients come from the recurrence of their differential
//!   equation and a few initial values from the series engine, and the guess is proven from that recurrence,
//! - otherwise the coefficients come from the series engine, and the guess is proven by checking the
//!   differential equation it implies on `f`, by simplification.
//!
//! Unproven guesses are rejected. The solution in each residue class modulo `m` is a product of the rational
//! function `{$Q / P$}`, computed by [`Term::product`]. Functions without such a recurrence are split: rational
//! functions into partial fractions, sums term by term.
//!
//! The result is a held sum `@sum` (see [`Context::held_sum`]), since `sum` would evaluate it back to `f`.

use malachite::{
    Integer, Natural, Rational,
    base::{
        num::{
            arithmetic::traits::{Abs, FloorRoot, Lcm, Pow},
            basic::traits::Zero,
            conversion::traits::RoundingFrom,
            logic::traits::SignificantBits,
        },
        rounding_modes::RoundingMode,
    },
};

use std::{cmp::Ordering, convert::Infallible};

use crate::{field::complex::C, solve::polynomial::PolynomialRoots};

use crate::{
    context::{
        Context, Symbol,
        assumptions::{Assumption, Assumptions, AssumptionsGuard, SignSet},
    },
    field::real::{
        R, approx,
        expr::{
            Expr, Real, arg, constant_sign, depends, fun, has_special_constant, infinity_sign, map_tree, one, size, subs,
            try_map_operands, unary, value, variable, zero,
        },
    },
    limit::{Direction, LimitError, LimitResult, series_terms},
    matrix::eigen,
    polynom::{
        dense::{Coefficient, Poly},
        fraction::{EPoly, Elem, sample_points, solve_linear, solve_linear_unique},
    },
    term::{Expand, Fun, Normalize, Term},
};

use super::{
    super::{holonomic, integrate::rational},
    field::Params,
    integer_index, is_rational_function,
    product::{combine_factorials, duplicate_gammas},
    tidy,
};

/// Absolute order in `w` up to which coefficients are computed.
const ORDER: i64 = 30;
/// Most coefficients used, for series with very negative or fractional exponents.
const MAX_COEFFICIENTS: usize = 64;
/// Largest period `m` of a recurrence.
const MAX_PERIOD: usize = 4;
/// Largest degree of the polynomials `P` and `Q` of a recurrence.
const MAX_DEGREE: usize = 4;
/// First index at which a recurrence must hold, the earlier coefficients being allowed to be irregular, like
/// `{$c_0 = 0$}` for `{$ln(1 + x)$}`.
const START: usize = 2;
/// Number of non-trivial equations of a recurrence beyond its unknowns, which check the guess.
const CHECKS: usize = 8;
/// Largest natural root of `P` looked for: beyond it, roots are assumed absent.
const MAX_ROOT: u64 = 10_000;

/// A recurrence `{$P(n) c_(n + m) = Q(n) c_n$}` for `{$n >= s$}`.
struct Recurrence {
    period: usize,
    start: usize,
    p: EPoly,
    q: EPoly,
}

impl Term<Real> {
    /// The whole series of the expression when `x` tends to `point` (from the side given by `direction`), as sums
    /// of its general terms, with powers of `{$x - a$}` (of `{$1/x$}` at `{$plus.minus oo$}`).
    ///
    /// # Errors
    /// [`LimitError::Unsupported`] when the coefficients have no recurrence found, like for `{$tan(x)$}`, the
    /// errors of [`Term::series`] otherwise.
    ///
    /// ```
    /// use formalith::{field::real::R, limit::Direction, parse, printer::{Print, PrintOptions}, symbol};
    ///
    /// let x = symbol!("x");
    /// let series = parse!("sin(x)", R).infinite_series(x, &parse!("0", R), Direction::Both).unwrap();
    /// assert_eq!(
    ///     series.with_options(PrintOptions::typst()).to_string(),
    ///     "sum_(k = 0)^(oo) frac(x^(2 k+1) (-1)^k, (2 k+1)!)"
    /// );
    /// ```
    pub fn infinite_series(
        &self,
        x: Symbol,
        point: &Self,
        direction: Direction,
    ) -> LimitResult<Self> {
        profile_scope!("series");
        let k = index(self, point);
        whole_series(self, x, point, direction, k, true)
    }
}

/// The index of the sums: `k`, or the first of `n`, `k_1`, `k_2`... not in the expression or the point.
// Some name of the infinite sequence is unused
#[allow(clippy::maybe_infinite_iter)]
fn index(f: &Expr, point: &Expr) -> Symbol {
    let mut used = f.symbols();
    used.extend(point.symbols());
    ["k".to_string(), "n".to_string()]
        .into_iter()
        .chain((1..).map(|i| format!("k_{i}")))
        .map(Symbol::new)
        .find(|s| !used.contains(s))
        .unwrap_or_else(|| unreachable!())
}

/// The series of `f`, guessed as a whole, then from its partial fractions or its terms when `split` is set.
fn whole_series(
    f: &Expr,
    x: Symbol,
    point: &Expr,
    direction: Direction,
    k: Symbol,
    split: bool,
) -> LimitResult<Expr> {
    if let Some(res) = known_series(f, x, point, direction, k) {
        return Ok(res);
    }
    let res = split_series(f, x, point, direction, k, split);
    if res.is_err() && split && is_rational_function(f) && f.symbols().len() == 1 {
        return rational_series(f, x, point, direction, k).or(res);
    }
    res
}

/// The series of `f` from the partial fractions over the roots of its denominator, which must be simple: a real
/// root `r` gives `{$A / (w - r) = -A rho / (1 - rho w)$}` with `{$rho = 1 / r$}` and `{$A = N(r) / D'(r)$}`, a pair of
/// complex roots, the roots of an irreducible quadratic factor `q`, gives
/// `{$(a + b w) / (1 - p w + s w^2) = sum r^n (a cos(n theta) + (a p + 2b) / sqrt(4s - p^2) sin(n theta)) w^n$}`
/// with `{$r = sqrt(s)$}` and `{$cos theta = p / (2 r)$}`. For rational functions with rational coefficients whose
/// irreducible factors aren't linear, like `{$1 / (1 - x - x^2)$}` or `{$1 / (1 - x + 2 x^2)$}`, whose coefficients
/// satisfy a recurrence with constant coefficients (no two-term one).
fn rational_series(
    f: &Expr,
    x: Symbol,
    point: &Expr,
    direction: Direction,
    k: Symbol,
) -> LimitResult<Expr> {
    let w = Symbol::new("@hw");
    let g = f
        .substitute(x, &substitution(point, direction, &variable(w)))
        .ok_or(LimitError::Unsupported)?;
    let mut params = Params::default();
    let (num, den) = params.rational(&g, w).ok_or(LimitError::Unsupported)?;
    let rational = |p: &EPoly| {
        p.coefficients()
            .iter()
            .map(|c| c.as_rational().cloned())
            .collect::<Option<Vec<_>>>()
            .map(Poly::new)
    };
    let (num, den) = (
        rational(&num).ok_or(LimitError::Unsupported)?,
        rational(&den).ok_or(LimitError::Unsupported)?,
    );
    if den.coefficient(0) == 0u32 {
        return Err(LimitError::Unsupported);
    }
    let (quotient, rest) = num.div_rem(&den);
    let n = variable(k);
    let simple = den.gcd(&den.derivative()).degree() == 0;
    let general = simple
        .then(|| simple_poles(&den, &rest, w, &n).ok())
        .flatten()
        .map_or_else(|| general_poles(&rest, &den, &n), Ok)?;
    let back = w_of_x(point, direction, x);
    // The first coefficients, with the polynomial part, by dividing the power series, then the general term
    let first = quotient.coefficients().len();
    let res = power_series(&num, &den, first)
        .into_iter()
        .enumerate()
        .fold(zero(), |res, (i, c)| {
            res + value(c) * w_power(&back, &value(Rational::from(i)))
        });
    let _guard = integer_index(k);
    let general = tidy(&(general * w_power(&back, &n)));
    Ok(res + held_sum(general, k, value(Rational::from(first))))
}

/// The first `count` coefficients of the power series of `{$N / D$}`, `{$D(0) != 0$}`.
fn power_series(num: &Poly, den: &Poly, count: usize) -> Vec<Rational> {
    let mut coefficients: Vec<Rational> = vec![];
    for i in 0..count {
        let c = (1..=i).fold(num.coefficient(i), |c, j| {
            c - den.coefficient(j) * &coefficients[i - j]
        }) / den.coefficient(0);
        coefficients.push(c);
    }
    coefficients
}

/// The coefficient of `{$w^n$}` of the proper fraction `{$R / D$}` for a square-free `D`, over its real roots and
/// the pairs of complex roots of its irreducible quadratic factors, see [`rational_series`].
fn simple_poles(den: &Poly, rest: &Poly, w: Symbol, n: &Expr) -> LimitResult<Expr> {
    let wv = variable(w);
    let term = |p: &Poly| {
        p.coefficients()
            .iter()
            .enumerate()
            .fold(zero(), |res, (i, c)| {
                res + value(c.clone()) * wv.pow(&value(Rational::from(i)))
            })
    };
    let (rest_term, derivative) = (term(rest), term(&den.derivative()));
    let mut general = zero();
    for q in rational::factor(den, w) {
        let [q0, q1, q2] = q.coefficients() else {
            general += real_poles(&q, &rest_term, &derivative, w, n)?;
            continue;
        };
        if q1 * q1 - Rational::from(4) * q0 * q2 >= 0u32 {
            general += real_poles(&q, &rest_term, &derivative, w, n)?;
            continue;
        }
        // `{$q = q_0 (1 - p w + s w^2)$}`, and the part `{$P / q$}` of the partial fractions, `{$P = a + b w$}`
        let (p, s) = (-(q1 / q0), q2 / q0);
        let cofactor = den.exact_div(&q);
        let numerator = rest.mul(&cofactor.inverse_mod(&q)).rem(&q);
        let (a, b) = (numerator.coefficient(0) / q0, numerator.coefficient(1) / q0);
        let root = |r: Rational| value(r).pow(&value(Rational::from_signeds(1, 2)));
        let discriminant = Rational::from(4) * &s - &p * &p;
        let theta = arg(
            &value(&p / Rational::from(2)),
            &(root(discriminant.clone()) / value(Rational::from(2))),
        )
        .ok_or(LimitError::Unsupported)?;
        let angle = n * &theta;
        general += value(s).pow(&(n / &value(Rational::from(2))))
            * (value(a.clone()) * fun(Context::COS, angle.clone())
                + value(a * p + Rational::from(2) * b) / root(discriminant)
                    * fun(Context::SIN, angle));
    }
    Ok(general)
}

/// The coefficient of `{$w^n$}` of the proper fraction `{$R / D$}` for any `D` with `{$D(0) != 0$}`: for each
/// irreducible factor `q` of `D` with multiplicity `e`, `{$sum_(l < e) n^l sum_rho A_l(rho) rho^n$}` over the roots
/// `{$rho$}` of the reversed `q`, `{$A_l in QQ[t]$}` of degree below that of `q`. Sums over conjugate roots are
/// power sums of the reversed `q`, rational, so the coefficients of the `{$A_l$}` solve a linear system over `{$QQ$}`
/// on the first coefficients of the series. The roots are written with radicals in `{$CC$}`, a pair `{$u plus.minus i v$}`
/// giving `{$2 |rho|^n (Re A_l(rho) cos(n theta) - Im A_l(rho) sin(n theta))$}`, `{$theta = arg(u + i v)$}`.
fn general_poles(rest: &Poly, den: &Poly, n: &Expr) -> LimitResult<Expr> {
    /// Equations checking the solution, beyond the unknowns.
    const CHECKS: usize = 8;
    let w = Symbol::new("@hw");
    let mut factors = vec![];
    for (i, part) in den.square_free().iter().enumerate() {
        if part.degree() > 0 {
            factors.extend(rational::factor(part, w).into_iter().map(|q| (q, i + 1)));
        }
    }
    // `{$q(w) = q_0 product (1 - rho w)$}`, the `{$rho$}` being the roots of the reversed `q`
    let reversed: Vec<(Poly, usize)> = factors
        .iter()
        .map(|(q, e)| {
            let mut coefficients = q.coefficients().to_vec();
            coefficients.reverse();
            (Poly::new(coefficients).monic(), *e)
        })
        .collect();
    let unknowns: usize = reversed.iter().map(|(q, e)| q.degree() * e).sum();
    let rows = unknowns + CHECKS;
    let degree = reversed.iter().map(|(q, _)| q.degree()).max().unwrap_or(0);
    let sums: Vec<Vec<Rational>> = reversed
        .iter()
        .map(|(q, _)| power_sums(q, rows + degree))
        .collect();
    let coefficients = power_series(rest, den, rows);
    let equations = (0..rows)
        .map(|row| {
            let mut equation = vec![];
            for ((q, e), sums) in reversed.iter().zip(&sums) {
                for l in 0..*e {
                    let scale = Rational::from(row).pow(u64::try_from(l).unwrap_or(0));
                    for t in 0..q.degree() {
                        equation.push(&scale * &sums[row + t]);
                    }
                }
            }
            equation.push(coefficients[row].clone());
            equation
        })
        .collect();
    let solution = solve_linear_unique(equations, unknowns).ok_or(LimitError::Unsupported)?;
    let mut general = zero();
    let mut offset = 0;
    for (q, e) in &reversed {
        let roots = root_parts(q).ok_or(LimitError::Unsupported)?;
        for l in 0..*e {
            let a = &solution[offset..offset + q.degree()];
            offset += q.degree();
            let mut part = zero();
            for (u, v) in &roots {
                // `{$A(u + i v)$}` by Horner's rule on the parts
                let (alpha, beta) = a.iter().rev().fold((zero(), zero()), |(re, im), c| {
                    (
                        (&re * u - &im * v + value(c.clone())).expand(),
                        (&re * v + &im * u).expand(),
                    )
                });
                let (u, v) = (u.clone(), v.clone());
                match constant_sign(&v).ok_or(LimitError::Unsupported)? {
                    Ordering::Less => {}
                    Ordering::Equal => part += alpha * u.pow(n),
                    Ordering::Greater => {
                        let theta = arg(&u, &v).ok_or(LimitError::Unsupported)?;
                        let modulus = (&u * &u + &v * &v).expand();
                        let angle = n * &theta;
                        part += value(Rational::from(2))
                            * modulus.pow(&(n / &value(Rational::from(2))))
                            * (alpha * fun(Context::COS, angle.clone())
                                - beta * fun(Context::SIN, angle));
                    }
                }
            }
            general += n.pow(&value(Rational::from(l))) * part;
        }
    }
    Ok(general)
}

/// The roots of the polynomial `q` with rational coefficients as their parts `{$(u, v)$}`, with radicals: from the roots
/// in `{$CC$}`, or else the real roots (as `rootof`) and a single pair of complex roots from Vieta's formulas
/// (`{$u = s / 2$}`, `{$v = sqrt(p - u^2)$}` for their sum `s` and product `p`). `None` when they aren't found.
fn root_parts(q: &Poly) -> Option<Vec<(Expr, Expr)>> {
    let complex = |c: &Rational| Term::constant([c.clone(), Rational::ZERO], C);
    let coefficients: Vec<_> = q.coefficients().iter().map(complex).collect();
    if let Some(roots) = <C<R<Rational>> as PolynomialRoots>::roots(&coefficients)
        && roots.len() == q.degree()
        && let Some(parts) = roots.iter().map(rational::split).collect::<Option<Vec<_>>>()
    {
        return Some(parts);
    }
    // As `rootof`, whose powers reduce canonically and which approximate quickly (radicals from Cardano's formula
    // are slow in the general terms)
    let real: Vec<Expr> = crate::field::real::rootof::real_roots(q);
    if real.len() + 2 != q.degree() {
        return None;
    }
    // `{$q$}` is monic: the sum of its roots is `{$-q_(d - 1)$}`, their product `{$(-1)^d q_0$}`
    let d = q.degree();
    let sum = real
        .iter()
        .fold(-value(q.coefficient(d - 1)), |res, r| res - r);
    let sign = if d % 2 == 0 { Rational::from(1) } else { Rational::from(-1) };
    let product = real
        .iter()
        .fold(value(sign * q.coefficient(0)), |res, r| res / r.clone());
    let u = (sum / value(Rational::from(2))).expand();
    let v = (product - &u * &u).expand().pow(&value(Rational::from_signeds(1, 2)));
    let mut parts: Vec<(Expr, Expr)> = real.into_iter().map(|r| (r, zero())).collect();
    parts.push((u.clone(), v.clone()));
    parts.push((u, -v));
    Some(parts)
}

/// The power sums `{$p_m = sum rho^m$}` of the roots of the monic `q`, for `{$m < "count"$}`, by Newton's identities.
fn power_sums(q: &Poly, count: usize) -> Vec<Rational> {
    let d = q.degree();
    let c = |i: usize| q.coefficient(i);
    let mut sums: Vec<Rational> = vec![];
    for m in 0..count {
        if m == 0 {
            sums.push(Rational::from(d));
            continue;
        }
        let mut p = Rational::ZERO;
        for i in 1..=m.min(d) {
            if i < m {
                p -= c(d - i) * &sums[m - i];
            }
        }
        if m <= d {
            p -= Rational::from(m) * c(d - m);
        }
        sums.push(p);
    }
    sums
}

/// The coefficient of `{$w^n$}` of the partial fractions of `{$N / D$}` over the roots of its factor `q`, which must
/// be real and simple: `{$B rho^n$}` for each root `r` of `q`, `{$rho = 1 / r$}`, with `D'` its derivative.
fn real_poles(q: &Poly, rest: &Expr, derivative: &Expr, w: Symbol, n: &Expr) -> LimitResult<Expr> {
    let wv = variable(w);
    // `{$q(w) = q_0 product_i (1 - rho_i w)$}`, the `{$rho_i$}` being the roots of the reversed polynomial
    let reversed = q
        .coefficients()
        .iter()
        .rev()
        .enumerate()
        .fold(zero(), |res, (i, c)| {
            res + value(c.clone()) * wv.pow(&value(Rational::from(i)))
        });
    let roots = eigen::real_roots(&reversed, w).ok_or(LimitError::Unsupported)?;
    if roots.len() != q.degree() || roots.iter().any(|(_, m)| *m != 1) {
        return Err(LimitError::Unsupported);
    }
    let mut res = zero();
    for (rho, _) in &roots {
        let r = (one() / rho.clone()).simplify();
        let at = |p: &Expr| p.substitute(w, &r).map(|t| t.expand());
        let a = at(rest).ok_or(LimitError::Unsupported)?
            / at(derivative).ok_or(LimitError::Unsupported)?;
        let b = (-(a * rho)).simplify();
        res += b * rho.pow(n);
    }
    Ok(res)
}

/// The series of `f`, guessed as a whole, then from its partial fractions or its terms when `split` is set.
fn split_series(
    f: &Expr,
    x: Symbol,
    point: &Expr,
    direction: Direction,
    k: Symbol,
    split: bool,
) -> LimitResult<Expr> {
    let whole = guess_series(f, x, point, direction, k);
    if !split || whole == Err(LimitError::Undefined) {
        return whole;
    }
    let rational = |f: &Expr| is_rational_function(f) && f.symbols().len() == 1;
    let parts = if rational(f) && whole.is_err() {
        f.apart(x).unwrap_or_else(|| f.clone())
    } else if matches!(f, Term::Mul(_)) && whole.is_err() {
        // A polynomial factor distributed, `{$(x + 1) arctan x = x arctan x + arctan x$}`
        f.expand()
    } else {
        f.clone()
    };
    let Term::Add(add) = &parts else {
        return whole;
    };
    // Rational terms of other sums are split into their partial fractions too
    let split = add
        .iter()
        .map(|term| whole_series(term, x, point, direction, k, !rational(f) && rational(term)))
        .collect::<LimitResult<Vec<_>>>()
        .map(|parts| merge_sums(&parts, x));
    // The one with the fewest sums, like `{$sum x^k/k! + sum (-1)^k x^(2k+1)/(2k+1)!$}` for `{$e^x + sin x$}`
    // rather than three sums with a period 4, and the whole one for `{$e^x - 1 - x$}`
    match (whole, split) {
        (Ok(whole), Ok(split)) => {
            if (held_sums(&split), size(&split)) < (held_sums(&whole), size(&whole)) {
                Ok(split)
            } else {
                Ok(whole)
            }
        }
        (Ok(res), Err(_)) | (Err(_), Ok(res)) => Ok(res),
        (Err(error), Err(_)) => Err(error),
    }
}

/// The number of held sums of a series.
fn held_sums(term: &Expr) -> usize {
    match term {
        Term::Add(add) => add.iter().map(held_sums).sum(),
        Term::Fun(fun) if fun.get_ident() == Context::held_sum() => 1,
        _ => 0,
    }
}

/// The sum of the series of the parts, held sums with the same bounds whose terms differ by a factor free of `x`
/// being merged, like `{$sum 2^(k + 1) x^k - sum x^k = sum (2^(k + 1) - 1) x^k$}`.
fn merge_sums(parts: &[Expr], x: Symbol) -> Expr {
    let mut sums: Vec<[Expr; 3]> = vec![];
    let mut res = zero();
    let terms = parts.iter().flat_map(|part| match part {
        Term::Add(add) => add.iter().cloned().collect(),
        _ => vec![part.clone()],
    });
    for term in terms {
        let args = match &term {
            Term::Fun(fun) if fun.get_ident() == Context::held_sum() => fun.get_args::<Real>(),
            _ => None,
        };
        let Some([body, k, a, _]) = args.as_ref().map(|args| args.as_slice()) else {
            res += term;
            continue;
        };
        match sums
            .iter_mut()
            .find(|[other, j, b]| j == k && !depends(&(body / &*other).simplify(), x) && start_gap(a, b).is_some())
        {
            Some([other, j, b]) => {
                // The leading terms of the sum starting first, explicit
                let Term::Symbol(index) = &*j else { unreachable!() };
                let _guard = integer_index(index.symbol);
                let gap = start_gap(a, b).unwrap_or(0);
                let (early, late) = if gap > 0 { (other.clone(), body.clone()) } else { (body.clone(), other.clone()) };
                let first = if gap > 0 { b.clone() } else { a.clone() };
                for i in 0..gap.abs() {
                    res += subs(&early, index.symbol, &(&first + &value(Rational::from(i))));
                }
                *b = &first + &value(Rational::from(gap.abs()));
                *other = early + late;
            }
            None => sums.push([body.clone(), k.clone(), a.clone()]),
        }
    }
    sums.into_iter().fold(res, |res, [body, k, a]| {
        let Term::Symbol(k) = k else { unreachable!() };
        res + held_sum(tidy_term(&body, k.symbol), k.symbol, a)
    })
}

/// `{$a - b$}` for integer starts of held sums at most [`MAX_START_GAP`] apart.
fn start_gap(a: &Expr, b: &Expr) -> Option<i64> {
    /// The largest difference between the starts of merged sums.
    const MAX_START_GAP: i64 = 4;
    let (Term::Value(a), Term::Value(b)) = (a, b) else {
        return None;
    };
    let gap = i64::try_from(&(&a.value - &b.value)).ok()?;
    (gap.abs() <= MAX_START_GAP).then_some(gap)
}

/// The first coefficients of a series in `w`: `{$c_j$}` is the coefficient of `{$w^(e_0 + j/q)$}`.
struct Coefficients {
    /// The expression `w` in `x`.
    w: Expr,
    e0: Rational,
    q: Rational,
    values: Vec<Expr>,
    elems: Vec<Elem>,
    params: Params,
}

/// The coefficients of the series of `f` from the series engine, or the whole series when it is finite.
fn coefficients(
    f: &Expr,
    x: Symbol,
    point: &Expr,
    direction: Direction,
) -> LimitResult<Result<Coefficients, Expr>> {
    // A polynomial of degree `d` has its whole series below `{$w^(d + 1)$}`
    let degree = Params::default().poly(f, x).map_or(0, |p| p.degree());
    let order = Rational::from(ORDER.max(i64::try_from(degree).unwrap_or(ORDER) + 1));
    let series = series_terms(f, x, point, &order, direction)?;
    let w = series.w;
    if series.exact {
        return Ok(Err(series.terms.iter().fold(zero(), |res, (e, c)| {
            res + c * &w_power(&w, &value(e.clone()))
        })));
    }
    let Some((e0, _)) = series.terms.first() else {
        return Err(LimitError::Unsupported);
    };
    let e0 = e0.clone();
    // Exponents `{$e_0 + j/q$}`
    let q = series.terms.iter().fold(Natural::from(1u32), |q, (e, _)| {
        q.lcm((e - &e0).into_denominator())
    });
    let q = Rational::from(q);
    let count = usize::try_from(
        &Integer::rounding_from((Rational::from(ORDER) - &e0) * &q, RoundingMode::Ceiling).0,
    )
    .map_err(|_| LimitError::Unsupported)?
    .min(MAX_COEFFICIENTS);
    let mut coefficients = vec![zero(); count];
    for (e, c) in &series.terms {
        let j = usize::try_from(&Integer::rounding_from((e - &e0) * &q, RoundingMode::Exact).0)
            .map_err(|_| LimitError::Unsupported)?;
        if j < count {
            coefficients[j] = c.clone();
        }
    }
    let mut params = Params::default();
    let elems = coefficients
        .iter()
        .map(|c| params.elem(c))
        .collect::<Option<Vec<_>>>()
        .ok_or(LimitError::Unsupported)?;
    Ok(Ok(Coefficients {
        w,
        e0,
        q,
        values: coefficients,
        elems,
        params,
    }))
}

/// The proven recurrence of the coefficients of a holonomic function, with its initial values.
struct Proven {
    recurrence: holonomic::recurrence::Recurrence,
    initial: Vec<(usize, Elem)>,
}

/// `w` in terms of `x`, the inverse of [`substitution`].
fn w_of_x(point: &Expr, direction: Direction, x: Symbol) -> Expr {
    match infinity_sign(point) {
        Some(sign) => value(Rational::from(sign as i64)) / variable(x),
        None if direction == Direction::Left => point - &variable(x),
        None => variable(x) - point.clone(),
    }
}

/// A function whose series at 0 has Bernoulli or Euler numbers as coefficients, so no recurrence.
#[derive(Clone, Copy)]
enum Kernel {
    Tan,
    Tanh,
    Sec,
    Sech,
    Csc,
    Csch,
    Cot,
    Coth,
    /// `{$1 / (e^t - 1)$}`
    ExpMinusOne,
}

impl Kernel {
    /// The terms of the series in `t`: explicit terms `{$c t^e$}`, then `{$sum_(k >= s) c_k t^(e_k)$}` as
    /// `{$(c_k, e_k, s)$}`.
    fn series(self, k: Symbol) -> (Vec<(Expr, i64)>, Expr, Expr, i64) {
        let n = variable(k);
        let int = |i: i64| value(Rational::from(i));
        let two_n = &int(2) * &n;
        let four_n = int(4).pow(&n);
        let sign = |shift: i64| int(-1).pow(&(&n + &int(shift)));
        let bernoulli =
            fun(Context::BERNOULLI, two_n.clone()) / fun(Context::FACTORIAL, two_n.clone());
        let euler = fun(Context::EULER, two_n.clone()) / fun(Context::FACTORIAL, two_n.clone());
        let odd = &two_n - &int(1);
        match self {
            // `{$tan t = sum_(k >= 1) (-1)^(k - 1) 4^k (4^k - 1) B_(2k) t^(2k - 1) / (2k)!$}`
            Self::Tan => (
                vec![],
                sign(-1) * &four_n * (&four_n - &int(1)) * bernoulli,
                odd,
                1,
            ),
            Self::Tanh => (vec![], &four_n * &(&four_n - &int(1)) * bernoulli, odd, 1),
            // `{$1 / cos t = sum_(k >= 0) (-1)^k E_(2k) t^(2k) / (2k)!$}`
            Self::Sec => (vec![], sign(0) * euler, two_n, 0),
            Self::Sech => (vec![], euler, two_n, 0),
            // `{$1 / sin t = sum_(k >= 0) (-1)^(k + 1) (4^k - 2) B_(2k) t^(2k - 1) / (2k)!$}`
            Self::Csc => (vec![], sign(1) * (&four_n - &int(2)) * bernoulli, odd, 0),
            Self::Csch => (vec![], -((&four_n - &int(2)) * bernoulli), odd, 0),
            // `{$cot t = sum_(k >= 0) (-1)^k 4^k B_(2k) t^(2k - 1) / (2k)!$}`
            Self::Cot => (vec![], sign(0) * four_n * bernoulli, odd, 0),
            Self::Coth => (vec![], four_n * bernoulli, odd, 0),
            // `{$1 / (e^t - 1) = 1/t - 1/2 + sum_(k >= 1) B_(2k) t^(2k - 1) / (2k)!$}`
            Self::ExpMinusOne => (
                vec![(one(), -1), (value(Rational::from_signeds(-1, 2)), 0)],
                bernoulli,
                odd,
                1,
            ),
        }
    }
}

/// The kernel of `factors`, with its argument and a constant factor: `{$tan t$}`, `{$(cos t)^(-1)$}`,
/// `{$cos t (sin t)^(-1)$}`, `{$(b e^t - b)^(-1)$}`...
fn kernel(factors: &[&Expr]) -> Option<(Kernel, Expr, Expr)> {
    let inverse = |t: &Expr| match t {
        Term::Pow(pow) if **pow.exponant == value(Rational::from(-1)) => Some((*pow.base).clone()),
        _ => None,
    };
    match factors {
        [f] => {
            if let Some((ident @ (Context::TAN | Context::TANH), t)) = unary(f) {
                let kernel = if ident == Context::TAN {
                    Kernel::Tan
                } else {
                    Kernel::Tanh
                };
                return Some((kernel, t.clone(), one()));
            }
            let base = inverse(f)?;
            if let Some((ident, t)) = unary(&base) {
                let kernel = match ident {
                    Context::COS => Kernel::Sec,
                    Context::COSH => Kernel::Sech,
                    Context::SIN => Kernel::Csc,
                    Context::SINH => Kernel::Csch,
                    Context::TAN => Kernel::Cot,
                    Context::TANH => Kernel::Coth,
                    _ => return None,
                };
                return Some((kernel, t.clone(), one()));
            }
            // `{$b e^t - b$}`
            let Term::Add(add) = &base else { return None };
            let [a, b] = add.iter().collect::<Vec<_>>()[..] else {
                return None;
            };
            let (exp, constant) = match (a, b) {
                (Term::Value(c), e) | (e, Term::Value(c)) => (e, c.value.clone()),
                _ => return None,
            };
            let (scale, exp) = match exp {
                Term::Mul(mul) if mul.iter().count() == 1 => {
                    (mul.coefficient.clone(), mul.iter().next()?)
                }
                _ => (Rational::from(1), exp),
            };
            match unary(exp) {
                Some((Context::EXP, t)) if constant == -&scale => {
                    Some((Kernel::ExpMinusOne, t.clone(), value(scale).inv()))
                }
                _ => None,
            }
        }
        [a, b] => {
            let (numerator, denominator) = match (inverse(a), inverse(b)) {
                (None, Some(d)) => (*a, d),
                (Some(d), None) => (*b, d),
                _ => return None,
            };
            match (unary(numerator)?, unary(&denominator)?) {
                ((Context::COS, t), (Context::SIN, u)) if t == u => {
                    Some((Kernel::Cot, t.clone(), one()))
                }
                ((Context::COSH, t), (Context::SINH, u)) if t == u => {
                    Some((Kernel::Coth, t.clone(), one()))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// The series of `{$C w^m K(alpha w)$}` for a [`Kernel`] `K`, `C` and `{$alpha$}` free of `w` and an integer `m`, in
/// terms of Bernoulli and Euler numbers, like `{$tan x$}` or `{$x / (e^x - 1)$}`.
fn known_series(
    f: &Expr,
    x: Symbol,
    point: &Expr,
    direction: Direction,
    k: Symbol,
) -> Option<Expr> {
    let w = Symbol::new("@hw");
    let wv = variable(w);
    let g = f.substitute(x, &substitution(point, direction, &wv))?;
    let (mut c, factors): (Expr, Vec<&Expr>) = match &g {
        Term::Mul(mul) => (value(mul.coefficient.clone()), mul.iter().collect()),
        _ => (one(), vec![&g]),
    };
    let mut m = 0;
    let mut kernel_factors = vec![];
    for factor in factors {
        if !depends(factor, w) {
            c *= factor;
        } else if *factor == wv {
            m += 1;
        } else if let Term::Pow(pow) = factor
            && *pow.base == wv
            && let Term::Value(e) = &**pow.exponant
            && let Ok(e) = i64::try_from(&e.value)
        {
            m += e;
        } else {
            kernel_factors.push(factor);
        }
    }
    let back = w_of_x(point, direction, x);
    let Some((kernel, t, scale)) = kernel(&kernel_factors) else {
        let factor = c * w_power(&back, &value(Rational::from(m)));
        let res = match kernel_factors[..] {
            [power] => kernel_power(power, w, x, point, direction, k)?,
            _ => product_series(&kernel_factors, w, &back, x, point, direction, k)?,
        };
        return Some(scale_held_sums(&res, &factor, x));
    };
    let alpha = (&t / &wv).normalize();
    let c = c * scale;
    if depends(&alpha, w) || alpha.is_zero() {
        return shifted_kernel(kernel, &t, w, k)
            .map(|res| scale_held_sums(&substitute_w(&res, w, &back, k), &(c * w_power(&back, &value(Rational::from(m)))), x));
    }
    let _guard = integer_index(k);
    let (explicit, general, exponent, start) = kernel.series(k);
    let mut res = zero();
    for (coefficient, e) in explicit {
        let e = value(Rational::from(e));
        res +=
            &c * &coefficient * alpha.pow(&e) * w_power(&back, &(&e + &value(Rational::from(m))));
    }
    let term = &c
        * &general
        * alpha.pow(&exponent)
        * w_power(&back, &(&exponent + &value(Rational::from(m))));
    Some(res + held_sum(tidy_term(&term, k), k, value(Rational::from(start))))
}

/// The series in `w` of the kernel `{$K(t)$}` at a regular point `{$t = beta + alpha w$}`, `{$beta != 0$}`, for `{$tan$}`,
/// `{$cot$}`, `{$1 / cos$}` and `{$1 / sin$}`, by their partial fractions (Mittag-Leffler): `{$cot z = sum_m 1/(z - m pi)$}`
/// gives `{$cot(beta + u) = sum_(n >= 0) c_n u^n$}` with `{$c_n = -D_n(beta / pi) / (n! pi^(n + 1))$}`, `{$D_n(q) =
/// psi^((n))(q) + (-1)^(n + 1) psi^((n))(1 - q)$}`, and likewise for the others. Written with the variable `w`, its
/// general term in `k` from `{$k = 1$}`; `None` at a pole or when `beta` isn't a constant.
fn shifted_kernel(kernel: Kernel, t: &Expr, w: Symbol, k: Symbol) -> Option<Expr> {
    let wv = variable(w);
    let beta = subs(t, w, &zero());
    let alpha = ((t - &beta) / wv.clone()).normalize();
    if beta.is_zero() || depends(&alpha, w) || alpha.is_zero() || depends(&beta, w) {
        return None;
    }
    let (sin, cos) = (fun(Context::SIN, beta.clone()), fun(Context::COS, beta.clone()));
    let regular = |f: &Expr| matches!(constant_sign(f), Some(Ordering::Less | Ordering::Greater));
    let n = variable(k);
    let pi = variable(Context::PI);
    let int = |i: i64| value(Rational::from(i));
    let polygamma = |q: Expr| {
        Term::Fun(Box::new(Fun::new(Context::POLYGAMMA, vec![n.clone(), q], R))).normalize()
    };
    let d = |q: Expr| polygamma(q.clone()) + int(-1).pow(&(&n + &int(1))) * polygamma(one() - q);
    let factorial = fun(Context::FACTORIAL, n.clone());
    let n1 = &n + &int(1);
    let q = &beta / &pi;
    let half = value(Rational::from_signeds(1, 2));
    // `{$1/sin z = sum_m (-1)^m/(z - m pi)$}`, the even and odd `m` giving the poles of `{$cot(z/2)$}`
    let csc = |q: Expr| {
        -(d(&q / &int(2)) - d((&q - &int(1)) / int(2))) / (factorial.clone() * (&int(2) * &pi).pow(&n1))
    };
    let (first, general) = match kernel {
        Kernel::Tan if regular(&cos) => (
            &sin / &cos,
            d(&q + &half) / (factorial.clone() * pi.pow(&n1)),
        ),
        Kernel::Cot if regular(&sin) => (&cos / &sin, -d(q) / (factorial.clone() * pi.pow(&n1))),
        Kernel::Csc if regular(&sin) => (one() / sin, csc(q)),
        // `{$1/cos z = 1/sin(z + pi/2)$}`
        Kernel::Sec if regular(&cos) => (one() / cos, csc(&q + &half)),
        _ => return None,
    };
    let _guard = integer_index(k);
    Some(first + held_sum(general * alpha.pow(&n) * wv.pow(&n), k, one()))
}

/// `res` in `w` (with held sums) with `w` replaced by `back`, its expression in `x`, each held sum tidied.
fn substitute_w(res: &Expr, w: Symbol, back: &Expr, k: Symbol) -> Expr {
    let terms: Vec<Expr> = match res {
        Term::Add(add) => add.iter().cloned().collect(),
        _ => vec![res.clone()],
    };
    let _guard = integer_index(k);
    terms.iter().fold(zero(), |res, term| {
        let term = match term {
            Term::Fun(fun) if fun.get_ident() == Context::held_sum() => {
                let Some([body, j, a, b]) = fun.get_args::<Real>().map(Vec::as_slice) else {
                    return res + term;
                };
                let body = replace_w(body, w, back);
                Term::Fun(Box::new(Fun::new(
                    Context::held_sum(),
                    vec![tidy_term(&body, k), j.clone(), a.clone(), b.clone()],
                    R,
                )))
                .normalize()
            }
            _ => replace_w(term, w, back),
        };
        res + term
    })
}

/// `term` with the powers `{$w^e$}` replaced by [`w_power`] of `back`.
fn replace_w(term: &Expr, w: Symbol, back: &Expr) -> Expr {
    map_tree(term, &|t| match t {
        Term::Symbol(s) if s.symbol == w => Some(back.clone()),
        Term::Pow(pow) if *pow.base == variable(w) => Some(w_power(back, &pow.exponant)),
        _ => None,
    })
}

/// `res` times `factor` free of the index, the factor moved into the terms of its held sums (with constants), whose
/// sums are then merged (see [`merge_sums`]) and leading terms cancelled by the other terms dropped.
fn scale_held_sums(res: &Expr, factor: &Expr, x: Symbol) -> Expr {
    let terms = linear_terms(res);
    let parts: Vec<Expr> = terms
        .iter()
        .map(|term| {
            let factors: Vec<&Expr> = match term {
                Term::Mul(mul) => mul.iter().collect(),
                _ => vec![term],
            };
            let sum = factors.iter().copied().find(
                |f| matches!(f, Term::Fun(fun) if fun.get_ident() == Context::held_sum()),
            );
            let Some(Term::Fun(sum)) = sum else {
                return term * factor;
            };
            let constant = term / &Term::Fun(sum.clone());
            let Some([body, Term::Symbol(j), a, b]) = sum.get_args::<Real>().map(Vec::as_slice)
            else {
                return term * factor;
            };
            if *b != variable(Context::OO) {
                return term * factor;
            }
            tidy_held_sum(&(constant * factor * body), j.symbol, a, x)
        })
        .collect();
    cancel_leading_terms(&merge_sums(&parts, x))
}

/// The terms of the sum `res`, constant factors of sums distributed: `{$-(a + b) = -a - b$}`.
fn linear_terms(res: &Expr) -> Vec<Expr> {
    match res {
        Term::Add(add) => add.iter().flat_map(linear_terms).collect(),
        Term::Mul(mul) => {
            let factors: Vec<&Expr> = mul.iter().collect();
            match factors.iter().position(|f| matches!(f, Term::Add(_))) {
                Some(i) if factors.iter().enumerate().all(|(j, f)| j == i || f.symbols().is_empty()) => {
                    let constant = factors
                        .iter()
                        .enumerate()
                        .filter(|(j, _)| *j != i)
                        .fold(value(mul.coefficient.clone()), |res, (_, f)| res * *f);
                    linear_terms(factors[i])
                        .into_iter()
                        .map(|t| &constant * &t)
                        .collect()
                }
                _ => vec![res.clone()],
            }
        }
        _ => vec![res.clone()],
    }
}

/// Leading terms of the held sums of `res` cancelled by its other terms dropped, like `{$-1 + sum_(k >= 1) c_k x^(2k - 2)$}`
/// with `{$c_1 = 1$}`.
fn cancel_leading_terms(res: &Expr) -> Expr {
    /// Most leading terms dropped per sum.
    const MAX_DROPPED: usize = 4;
    let terms: Vec<Expr> = match res {
        Term::Add(add) => add.iter().cloned().collect(),
        _ => vec![res.clone()],
    };
    let (sums, others): (Vec<Expr>, Vec<Expr>) = terms.into_iter().partition(
        |t| matches!(t, Term::Fun(fun) if fun.get_ident() == Context::held_sum()),
    );
    let mut rest = others.into_iter().fold(zero(), |res, t| res + t);
    let mut out = zero();
    for sum in sums {
        let Term::Fun(fun) = &sum else { unreachable!() };
        let Some([body, Term::Symbol(j), Term::Value(a), b]) =
            fun.get_args::<Real>().map(Vec::as_slice)
        else {
            out += sum;
            continue;
        };
        let _guard = integer_index(j.symbol);
        let mut start = a.value.clone();
        for _ in 0..MAX_DROPPED {
            if rest.is_zero() {
                break;
            }
            let first = subs(body, j.symbol, &value(start.clone()));
            let left = (&rest + &first).expand();
            if !left.is_zero() && size(&left) >= size(&rest) {
                break;
            }
            rest = left;
            start += Rational::from(1);
        }
        out += Term::Fun(Box::new(Fun::new(
            Context::held_sum(),
            vec![body.clone(), variable(j.symbol), value(start), b.clone()],
            R,
        )))
        .normalize();
    }
    out + rest
}

/// The series of the product of `factors` (in `w`), one of them having a known series (see [`known_series`]) and the
/// others a whole series, as their Cauchy product (see [`multiply_series`]): `{$tan(x) / (1 + x)$}`.
fn product_series(
    factors: &[&Expr],
    w: Symbol,
    back: &Expr,
    x: Symbol,
    point: &Expr,
    direction: Direction,
    k: Symbol,
) -> Option<Expr> {
    for (i, factor) in factors.iter().enumerate() {
        let Some(known) = known_series(&replace_w(factor, w, back), x, point, direction, k) else {
            continue;
        };
        let others = factors
            .iter()
            .enumerate()
            .filter(|(j, _)| *j != i)
            .fold(one(), |res, (_, f)| res * *f);
        // Polynomials in `w` are their own series, written in powers of `w`
        let expanded = others.expand();
        let series = if linear_terms(&expanded).iter().all(|t| is_power_of(t, w)) {
            linear_terms(&expanded)
                .iter()
                .map(|t| replace_w(t, w, back))
                .collect()
        } else {
            linear_terms(&whole_series(&replace_w(&others, w, back), x, point, direction, k, true).ok()?)
        };
        return multiply_series(&linear_terms(&known), &series, x, k);
    }
    None
}

/// Whether `t` is a constant times a natural power of `w`.
fn is_power_of(t: &Expr, w: Symbol) -> bool {
    let factors: Vec<&Expr> = match t {
        Term::Mul(mul) => mul.iter().collect(),
        _ => vec![t],
    };
    factors.iter().all(|f| match f {
        Term::Symbol(s) if s.symbol == w => true,
        Term::Pow(pow) => {
            *pow.base == variable(w)
                && matches!(&**pow.exponant, Term::Value(e) if e.value > 0u32 && e.value.denominator_ref() == &1u32)
        }
        _ => !depends(f, w),
    })
}

/// The product of two whole series of `x` given by their terms, explicit terms and held sums: explicit terms move into the sums (one per
/// term), and two sums `{$sum_(k >= a) A(k) w^(alpha k + beta)$}` and `{$sum_(k >= b) B(k) w^(k + delta)$}` (`w` being
/// the same power base, `{$alpha$}` 1 or 2) give `{$sum_(N >= alpha a + b) w^(N + beta + delta) sum_(j = a)^(floor((N -
/// b)/alpha)) A(j) B(N - alpha j)$}`. `None` for other sums.
fn multiply_series(a: &[Expr], b: &[Expr], x: Symbol, k: Symbol) -> Option<Expr> {
    let split = |e: &[Expr]| -> (Vec<Expr>, Vec<Expr>) {
        e.iter().cloned().partition(
            |t| matches!(t, Term::Fun(fun) if fun.get_ident() == Context::held_sum()),
        )
    };
    let ((sums_a, explicit_a), (sums_b, explicit_b)) = (split(a), split(b));
    let mut parts = vec![];
    for t in &explicit_a {
        for u in &explicit_b {
            parts.push(t * u);
        }
    }
    for (sums, explicit) in [(&sums_a, &explicit_b), (&sums_b, &explicit_a)] {
        for sum in sums {
            for t in explicit {
                parts.extend(linear_terms(&scale_held_sums(sum, t, x)));
            }
        }
    }
    for sa in &sums_a {
        for sb in &sums_b {
            parts.push(convolve(sa, sb, x, k)?);
        }
    }
    Some(cancel_leading_terms(&merge_sums(&parts, x)))
}

/// The Cauchy product of two held sums, see [`multiply_series`].
fn convolve(a: &Expr, b: &Expr, x: Symbol, k: Symbol) -> Option<Expr> {
    let parts = |sum: &Expr| {
        let Term::Fun(fun) = sum else { return None };
        let [body, Term::Symbol(j), Term::Value(start), _] = fun.get_args::<Real>()?.as_slice()
        else {
            return None;
        };
        let _guard = integer_index(j.symbol);
        let body = subs(body, j.symbol, &variable(k));
        let (c, base, e) = power_of(&body, x)?;
        let (alpha, beta) = affine(&e, k)?;
        Some((c, base, alpha, beta, start.value.clone()))
    };
    let (mut a, mut b) = (parts(a)?, parts(b)?);
    if b.2 != 1u32 {
        std::mem::swap(&mut a, &mut b);
    }
    let (ca, base, alpha, beta, a0) = a;
    let (cb, base_b, gamma, delta, b0) = b;
    if base != base_b || gamma != 1u32 || !(alpha == 1u32 || alpha == 2u32) {
        return None;
    }
    let j = Symbol::new(if [k, x].contains(&Symbol::new("j")) { "i" } else { "j" });
    let _guard = integer_index(k);
    let _inner = integer_index(j);
    let (n, jv) = (variable(k), variable(j));
    let alpha_v = value(alpha.clone());
    let term = subs(&ca, k, &jv) * subs(&cb, k, &(&n - &(&alpha_v * &jv)));
    let upper = if alpha == 1u32 {
        &n - &value(b0.clone())
    } else {
        fun(Context::FLOOR, (&n - &value(b0.clone())) / alpha_v.clone())
    };
    let inner = Term::Fun(Box::new(Fun::new(
        Context::SUM,
        vec![tidy_term(&term, j), jv, value(a0.clone()), upper],
        R,
    )))
    .normalize();
    let general = inner * base.pow(&(&n + &value(beta + delta)));
    Some(held_sum(general, k, value(alpha * a0 + b0)))
}

/// The series of `{$K^n$}`, `K` being `{$tan t$}`, `{$tanh t$}`, `{$cot t$}` or `{$coth t$}` with `{$t = alpha w$}` (or even
/// powers of `{$1/cos t$}`, `{$1/sin t$}` and their hyperbolic versions, written with them), from the Riccati equation
/// `{$K' = p + q K^2$}`: `{$K^n = ((K^(n - 1))' / (n - 1) - p K^(n - 2)) / q$}`, the series of `K` being differentiated
/// term by term. Only at finite points from the right, `{$x = a + w$}`, and for `{$2 <= n <= 6$}`.
fn kernel_power(
    factor: &Expr,
    w: Symbol,
    x: Symbol,
    point: &Expr,
    direction: Direction,
    k: Symbol,
) -> Option<Expr> {
    /// Largest power.
    const MAX_POWER: i64 = 6;
    const MIN_POWER: i64 = -MAX_POWER;
    if infinity_sign(point).is_some() || direction == Direction::Left {
        return None;
    }
    let Term::Pow(pow) = factor else {
        return None;
    };
    let Term::Value(e) = &**pow.exponant else {
        return None;
    };
    let e = i64::try_from(&e.value).ok()?;
    let (ident, t) = unary(&pow.base)?;
    let alpha = (t / &variable(w)).normalize();
    if depends(&alpha, w) || alpha.is_zero() {
        return None;
    }
    // The kernel, its Riccati coefficients `{$(p, q)$}`, and the polynomial in it of `factor`
    let (kernel, (p, q), polynomial): (Kernel, (i64, i64), Vec<i64>) = match (ident, e) {
        (Context::TAN, 2..=MAX_POWER) => (Kernel::Tan, (1, 1), monomial(e)),
        (Context::TANH, 2..=MAX_POWER) => (Kernel::Tanh, (1, -1), monomial(e)),
        (Context::TAN, MIN_POWER..=-2) => (Kernel::Cot, (-1, -1), monomial(-e)),
        (Context::TANH, MIN_POWER..=-2) => (Kernel::Coth, (1, -1), monomial(-e)),
        // `{$1/cos^2 = 1 + tan^2$}`, `{$1/cosh^2 = 1 - tanh^2$}`, `{$1/sin^2 = 1 + cot^2$}`, `{$1/sinh^2 = coth^2 - 1$}`
        (Context::COS, MIN_POWER..=-2) if e % 2 == 0 => (Kernel::Tan, (1, 1), binomial_power(1, 1, -e / 2)),
        (Context::COSH, MIN_POWER..=-2) if e % 2 == 0 => {
            (Kernel::Tanh, (1, -1), binomial_power(1, -1, -e / 2))
        }
        (Context::SIN, MIN_POWER..=-2) if e % 2 == 0 => (Kernel::Cot, (-1, -1), binomial_power(1, 1, -e / 2)),
        (Context::SINH, MIN_POWER..=-2) if e % 2 == 0 => {
            (Kernel::Coth, (1, -1), binomial_power(-1, 1, -e / 2))
        }
        _ => return None,
    };
    let t_x = &alpha * &(variable(x) - point.clone());
    let base = match kernel {
        Kernel::Tan => fun(Context::TAN, t_x),
        Kernel::Tanh => fun(Context::TANH, t_x),
        Kernel::Cot => one() / fun(Context::TAN, t_x),
        _ => one() / fun(Context::TANH, t_x),
    };
    let first = known_series(&base, x, point, direction, k)?;
    let (p, q) = (value(Rational::from(p)), value(Rational::from(q)));
    let mut powers = vec![one(), first];
    for j in 2..polynomial.len() {
        let previous = &powers[j - 1];
        let derivative = previous.derivative(x) / (&alpha * &value(Rational::from(j - 1)));
        powers.push((derivative - &p * &powers[j - 2]) / q.clone());
    }
    Some(
        polynomial
            .iter()
            .zip(&powers)
            .fold(zero(), |res, (c, power)| res + value(Rational::from(*c)) * power),
    )
}

/// The coefficients of `{$K^n$}` as a polynomial in `K`.
fn monomial(n: i64) -> Vec<i64> {
    let mut res = vec![0; usize::try_from(n).unwrap_or(0) + 1];
    if let Some(last) = res.last_mut() {
        *last = 1;
    }
    res
}

/// The coefficients of `{$(a + b K^2)^m$}` as a polynomial in `K`.
fn binomial_power(a: i64, b: i64, m: i64) -> Vec<i64> {
    let m = usize::try_from(m).unwrap_or(0);
    let mut res = vec![0; 2 * m + 1];
    for (i, c) in (0..=m).map(|i| (i, binomial_coefficient(m, i))) {
        res[2 * i] = c * a.pow(u32::try_from(m - i).unwrap_or(0)) * b.pow(u32::try_from(i).unwrap_or(0));
    }
    res
}

/// `{$binom(m, i)$}`.
fn binomial_coefficient(m: usize, i: usize) -> i64 {
    (0..i).fold(1, |res, j| res * i64::try_from(m - j).unwrap_or(0) / i64::try_from(j + 1).unwrap_or(1))
}

/// `x` in terms of `w`: `{$a + w$}`, `{$a - w$}` from the left, `{$s / w$}` at `{$s oo$}`.
fn substitution(point: &Expr, direction: Direction, w: &Expr) -> Expr {
    match infinity_sign(point) {
        Some(sign) => value(Rational::from(sign as i64)) / w,
        None if direction == Direction::Left => point - w,
        None => point + w,
    }
}

/// The coefficients of the series of `f`, computed from the recurrence of the differential equation of
/// `{$f w^(-e_0)$}` (see [`holonomic`]) and a few initial values from the series engine, so that they are
/// proven. `None` when `f` isn't holonomic by the rules of [`holonomic::dfinite`], for Puiseux series, and for
/// finite series.
fn holonomic_coefficients(
    f: &Expr,
    x: Symbol,
    point: &Expr,
    direction: Direction,
) -> LimitResult<Option<(Coefficients, Proven)>> {
    let mut low = series_terms(f, x, point, &Rational::from(4), direction)?;
    if low.terms.is_empty() && !low.exact {
        low = series_terms(f, x, point, &Rational::from(16), direction)?;
    }
    let Some((e0, _)) = low.terms.first() else {
        return Ok(None);
    };
    if low.exact || low.terms.iter().any(|(e, _)| e.denominator_ref() != &1u32) {
        return Ok(None);
    }
    let e0 = e0.clone();
    let w = Symbol::new("@hw");
    let Some(g) = f.substitute(x, &substitution(point, direction, &variable(w))) else {
        return Ok(None);
    };
    let g = g * variable(w).pow(&value(-&e0));
    let mut params = Params::default();
    let Some(recurrence) = holonomic::dfinite::annihilator(&g, w, &mut params).and_then(|op| {
        holonomic::recurrence::Recurrence::from_differential(&op.clear_denominators())
    }) else {
        return Ok(None);
    };
    let Some(indices) = recurrence.initial_indices() else {
        return Ok(None);
    };
    let count = indices.last().map_or(0, |i| i + 1);
    let series = series_terms(f, x, point, &(&e0 + Rational::from(count)), direction)?;
    let mut initial = vec![];
    for index in indices {
        let exponent = &e0 + Rational::from(index);
        let c = series
            .terms
            .iter()
            .find(|(e, _)| *e == exponent)
            .map_or_else(zero, |(_, c)| c.clone());
        initial.push((index, params.elem(&c).ok_or(LimitError::Unsupported)?));
    }
    let Some(elems) = recurrence.coefficients(&initial, MAX_COEFFICIENTS) else {
        return Ok(None);
    };
    let coefficients = elems.iter().map(|c| params.to_term(c)).collect();
    Ok(Some((
        Coefficients {
            w: series.w,
            e0,
            q: Rational::from(1),
            values: coefficients,
            elems,
            params,
        },
        Proven {
            recurrence,
            initial,
        },
    )))
}

/// Whether the guessed recurrence `{$P(n) c_(n + m) = Q(n) c_n$}` (for `{$n >= s$}`) holds for the coefficients
/// of `f`: with `{$t = w^(1/q)$}`, the tail `{$g(t) = f t^(-q e_0) - sum_(j < s) c_j t^j$}`, `{$theta = t d/(d t)$}`
/// and `{$h_0 = sum_(j = s)^(s + m - 1) c_j t^j$}`, it is equivalent to `{$P(theta - m)(g - h_0) = t^m Q(theta) g$}`,
/// checked by simplification (an undecided zero rejects it).
fn verify_by_ode(
    f: &Expr,
    x: Symbol,
    point: &Expr,
    direction: Direction,
    coefficients: &Coefficients,
    recurrence: &Recurrence,
) -> bool {
    let t = Symbol::new("@ht");
    let Ok(q) = u64::try_from(&coefficients.q) else {
        return false;
    };
    // `{$t > 0$}`, so that `{$sqrt(t^2) = t$}` keeps radicals of `{$x = t^q$}` algebraic
    let mut assumptions = Assumptions::current();
    if assumptions
        .assume(t, Assumption::sign(SignSet::POSITIVE))
        .is_err()
    {
        return false;
    }
    let _guard = assumptions.enter();
    let q_term = value(Rational::from(q));
    let Some(f_t) = f.substitute(
        x,
        &substitution(point, direction, &variable(t).pow(&q_term)),
    ) else {
        return false;
    };
    let (s, m) = (recurrence.start, recurrence.period);
    let power = |j: usize| variable(t).pow(&value(Rational::from(j)));
    let c = &coefficients.values;
    let head = (0..s).fold(zero(), |res, j| res + &c[j] * &power(j));
    let g = f_t * variable(t).pow(&(-&q_term * value(coefficients.e0.clone()))) - head;
    let h0 = (s..s + m).fold(zero(), |res, j| res + &c[j] * &power(j));
    let theta = |h: &Expr| variable(t) * h.derivative(t);
    // `{$P(theta - shift) h$}` by Horner's rule
    let to_term = |a: &Elem| coefficients.params.to_term(a);
    let apply = |p: &EPoly, h: &Expr, shift: usize| {
        let Some((lead, rest)) = p.coefficients().split_last() else {
            return zero();
        };
        let shift = value(Rational::from(shift));
        rest.iter().rev().fold(to_term(lead) * h, |res, a| {
            theta(&res) - &shift * &res + to_term(a) * h
        })
    };
    let e = apply(&recurrence.p, &(&g - &h0), m) - power(m) * apply(&recurrence.q, &g, 0);
    is_identically_zero(&e, t)
}

/// Largest expression whose zero test uses `simplify`, which may be slow on big expressions.
const MAX_SIMPLIFY_SIZE: usize = 80;

/// Whether `e`, a function of `{$t > 0$}` near 0, is zero: rejected quickly when it isn't zero at a few sample
/// points, then proven zero in the tower of its radicals (see [`holonomic::algebraic`]), by expansion or by
/// simplification. Undecided expressions aren't zero.
fn is_identically_zero(e: &Expr, t: Symbol) -> bool {
    let samples = [(1, 7), (2, 13), (1, 29)];
    let tiny = Rational::from_signeds(1, 1i64 << 40).pow(3u64);
    let nonzero = samples.iter().any(|&(p, q)| {
        let at = subs(e, t, &value(Rational::from_signeds(p, q)));
        approx::approximate_fixed(&at, 256).is_some_and(|v| v.abs() > tiny)
    });
    if nonzero {
        return false;
    }
    holonomic::algebraic::is_zero(e, t)
        || e.expand().is_zero()
        || (size(e) <= MAX_SIMPLIFY_SIZE && fun(Context::SIMPLIFY, e.clone()).is_zero())
}

/// The series of `f` from a recurrence of its coefficients.
fn guess_series(
    f: &Expr,
    x: Symbol,
    point: &Expr,
    direction: Direction,
    k: Symbol,
) -> LimitResult<Expr> {
    let (found, proven) = match holonomic_coefficients(f, x, point, direction)? {
        Some((found, proven)) => (found, Some(proven)),
        None => match coefficients(f, x, point, direction)? {
            Ok(found) => (found, None),
            Err(finite) => return Ok(finite),
        },
    };
    let recurrence = guess(&found.elems).ok_or(LimitError::Unsupported)?;
    // The guess must be proven: from the recurrence of a holonomic function, otherwise by its differential
    // equation
    let holds = match &proven {
        Some(proven) => proven.recurrence.proves(
            &proven.initial,
            &recurrence.p,
            &recurrence.q,
            recurrence.period,
            recurrence.start,
        ),
        None => verify_by_ode(f, x, point, direction, &found, &recurrence),
    };
    if !holds {
        return Err(LimitError::Unsupported);
    }
    let Coefficients {
        w,
        e0,
        q,
        values: coefficients,
        elems,
        params,
    } = found;
    let w = &w;
    let _guard = integer_index(k);
    // `{$w^(e_0 + j/q)$}`
    let exponent = |j: &Expr| value(e0.clone()) + j / &value(q.clone());
    let mut res = coefficients[..recurrence.start]
        .iter()
        .enumerate()
        .fold(zero(), |res, (j, c)| {
            res + c * &w_power(w, &exponent(&value(Rational::from(j))))
        });
    let l = Symbol::new("@j");
    let m = recurrence.period;
    let ratio = params.k_poly_to_term(&recurrence.q, l) / params.k_poly_to_term(&recurrence.p, l);
    for i in recurrence.start..recurrence.start + m {
        if elems[i].is_zero() {
            continue;
        }
        let i_term = value(Rational::from(i));
        let sum = if m == 1 {
            // `{$c_n = c_i product_(l = i)^(n - 1) Q(l) / P(l)$}`
            let n = variable(k);
            let c = &coefficients[i]
                * &ratio
                    .product(l, &i_term, &(&n - &value(Rational::from(1))))
                    .map_err(|_| LimitError::Unsupported)?;
            let term = c * w_power(w, &exponent(&n));
            if q == 1u32 && e0.denominator_ref() == &1u32 {
                // Indexed by the exponent of `w`
                let shifted = subs(&tidy_term(&term, k), k, &(&n - &value(e0.clone())));
                held_sum(tidy(&shifted), k, &i_term + &value(e0.clone()))
            } else {
                held_sum(tidy_term(&term, k), k, i_term)
            }
        } else {
            // `{$c_(m j + i) = c_i product_(l = 0)^(j - 1) Q(m l + i) / P(m l + i)$}`
            let m_term = value(Rational::from(m as u64));
            let shifted = subs(&ratio, l, &(&m_term * &variable(l) + &i_term));
            let c = &coefficients[i]
                * &shifted
                    .product(l, &zero(), &(variable(k) - value(Rational::from(1))))
                    .map_err(|_| LimitError::Unsupported)?;
            let n = &m_term * &variable(k) + &i_term;
            held_sum(tidy_term(&(c * w_power(w, &exponent(&n))), k), k, zero())
        };
        res += sum;
    }
    Ok(res)
}

/// `{$w^e$}`, as `{$(plus.minus 1)^e x^(-e)$}` for `{$w = plus.minus 1/x$}`.
fn w_power(w: &Expr, e: &Expr) -> Expr {
    match w {
        Term::Pow(pow) if **pow.exponant == value(Rational::from(-1)) => pow.base.pow(&-e),
        Term::Mul(mul) if mul.coefficient == -1 => {
            match mul.iter().collect::<Vec<_>>().as_slice() {
                [Term::Pow(pow)] if **pow.exponant == value(Rational::from(-1)) => {
                    value(Rational::from(-1)).pow(e) * pow.base.pow(&-e)
                }
                _ => w.pow(e),
            }
        }
        _ => w.pow(e),
    }
}

/// Leading terms of a held sum checked for zero by [`tidy_held_sum`].
const MAX_ZERO_TERMS: usize = 8;
/// Most leading terms of a held sum integrated separately, because they have a logarithm.
const MAX_LOG_TERMS: i64 = 16;

/// The derivative of the held sum `{$sum_(k = a)^oo f$}` of the arguments `[f, k, a, oo]` with respect to `x`, term
/// by term, which holds inside the disk of convergence of a whole series: `{$sum_(k >= 0) x^k / k!$}` gives itself.
pub fn derive_held_sum(args: &[Expr], x: Symbol) -> Option<Expr> {
    let [body, Term::Symbol(k), a, b] = args else {
        return None;
    };
    if k.symbol == x || depends(a, x) || *b != variable(Context::OO) {
        return None;
    }
    Some(tidy_held_sum(&body.derivative(x), k.symbol, a, x))
}

/// An antiderivative of the held sum `{$sum_(k = a)^oo f$}` of the arguments `[f, k, a, oo]` with respect to `x`,
/// term by term. For `{$f = C(k) B^E$}`, `B` being linear in `x` and `E` affine in `k`, it is
/// `{$C B^(E + 1) / ((E + 1) B')$}`, the terms where `{$E = -1$}` being integrated by `integrate`, giving logarithms.
/// Other terms with such a factor `{$B^E$}` are integrated by `integrate` with a symbolic `k` (natural, at least `a`),
/// as `{$G(x, k) - G(x_0, k)$}` with `{$B(x_0) = 0$}`, so that the terms vanish at the point of the series. `None`
/// for other terms.
pub fn integrate_held_sum(
    args: &[Expr],
    x: Symbol,
    integrate: &mut dyn FnMut(&Expr) -> Option<Expr>,
) -> Option<Expr> {
    let [body, Term::Symbol(k), Term::Value(a), b] = args else {
        return None;
    };
    let k = k.symbol;
    if k == x || *b != variable(Context::OO) {
        return None;
    }
    let mut start = Integer::try_from(&a.value).ok()?;
    let _guard = integer_index(k);
    let (base, e) = linear_power(body, x)?;
    let (alpha, beta) = affine(&e, k)?;
    let mut res = zero();
    if alpha == 0u32 {
        if beta == -1 {
            return None;
        }
    } else if let Ok(k0) = Integer::try_from(&((Rational::from(-1) - &beta) / &alpha))
        && k0 >= start
    {
        // `{$integral B^(-1) = ln|B| / B'$}` and the terms before
        if &k0 - &start > MAX_LOG_TERMS {
            return None;
        }
        while start <= k0 {
            res += integrate(&subs(body, k, &value(Rational::from(&start))))?;
            start += Integer::from(1);
        }
    }
    let first = value(Rational::from(&start));
    if let Some((c, power_base, e)) = power_of(body, x)
        && power_base == base
    {
        let e1 = e + one();
        let antiderivative = c * base.pow(&e1) / (e1 * base.derivative(x));
        return Some(res + tidy_held_sum(&antiderivative, k, &first, x));
    }
    // With a symbolic `k`, the terms vanishing at the root of `B` when `{$E > 0$}`
    if alpha <= 0u32 {
        return None;
    }
    let _natural = natural_index(k, &start);
    let antiderivative = integrate(body)?;
    if has_held_sum(&antiderivative) {
        return None;
    }
    let slope = base.derivative(x);
    let x0 = -subs(&base, x, &zero()) / slope;
    let at_x0 = antiderivative.limit(x, &x0, Direction::Right).ok()?;
    if depends(&at_x0, x) || has_special_constant(&at_x0) {
        return None;
    }
    Some(res + tidy_held_sum(&(antiderivative - at_x0), k, &first, x))
}

/// The held sum `{$sum_(k = a)^oo f(k)$}` of the arguments `[f, k, a, oo]` with `x` replaced by the constant `point`,
/// when it converges there by the ratio test (`{$lim_(k -> oo) |f(k + 1)/f(k)| < 1$}`), `None` otherwise. Zero when
/// every term vanishes.
pub fn held_sum_at(args: &[Expr], x: Symbol, point: &Expr) -> Option<Expr> {
    let [body, Term::Symbol(k), a, b] = args else {
        return None;
    };
    let k = k.symbol;
    if k == x || *b != variable(Context::OO) || depends(a, x) {
        return None;
    }
    let _guard = integer_index(k);
    // At the root of a factor `{$B^E$}` with `{$E > 0$}` for every `{$k >= a$}`, every term vanishes
    if let Some((base, e)) = linear_power(body, x)
        && subs(&base, x, point).expand().is_zero()
        && let Some((alpha, beta)) = affine(&e, k)
        && let Term::Value(a) = a
        && alpha >= 0u32
        && alpha * &a.value + beta > 0u32
    {
        return Some(zero());
    }
    let body = subs(body, x, point);
    if body.expand().is_zero() {
        return Some(zero());
    }
    let next = subs(&body, k, &(variable(k) + one()));
    let ratio = fun(Context::ABS, &next / &body);
    let limit = ratio.limit(k, &variable(Context::OO), Direction::Both).ok()?;
    (constant_sign(&(one() - limit)) == Some(Ordering::Greater))
        .then(|| tidy_held_sum(&body, k, a, x))
}

/// `{$S(b) - S(a)$}` for the held sum `S` of the arguments `[f, k, a, oo]` in `x`, as a single held sum, when it
/// converges at both points (see [`held_sum_at`]).
pub fn held_sum_between(args: &[Expr], x: Symbol, a: &Expr, b: &Expr) -> Option<Expr> {
    let (at_a, at_b) = (held_sum_at(args, x, a)?, held_sum_at(args, x, b)?);
    let [body, Term::Symbol(k), start, _] = args else {
        return None;
    };
    if at_a.is_zero() || at_b.is_zero() {
        return Some(at_b - at_a);
    }
    let _guard = integer_index(k.symbol);
    let difference = subs(body, x, b) - subs(body, x, a);
    Some(tidy_held_sum(&difference, k.symbol, start, x))
}

/// Whether `term` has a held sum.
pub fn has_held_sum(term: &Expr) -> bool {
    let found = std::cell::Cell::new(false);
    map_tree(term, &|t| {
        if let Term::Fun(f) = t
            && f.get_ident() == Context::held_sum()
        {
            found.set(true);
        }
        None
    });
    found.get()
}

/// Assume the index `k` of a held sum starting at `start` natural and at least `start`, as far as signs go.
fn natural_index(k: Symbol, start: &Integer) -> Option<AssumptionsGuard> {
    let mut assumptions = Assumptions::current();
    let sign = if *start >= 1u32 {
        SignSet::POSITIVE
    } else if *start >= 0u32 {
        SignSet::NONNEGATIVE
    } else {
        return None;
    };
    assumptions
        .assume(
            k,
            Assumption {
                sign,
                integer: true,
            },
        )
        .ok()?;
    Some(assumptions.enter())
}

/// The factor `{$B^E$}` of `body` with `B` linear in `x` and `E` free of `x`, depending on another symbol.
fn linear_power(body: &Expr, x: Symbol) -> Option<(Expr, Expr)> {
    let factors: Vec<&Expr> = match body {
        Term::Mul(mul) => mul.iter().collect(),
        _ => vec![body],
    };
    factors.into_iter().find_map(|factor| {
        let Term::Pow(pow) = factor else {
            return None;
        };
        let slope = pow.base.derivative(x);
        (!slope.is_zero()
            && !depends(&slope, x)
            && !depends(&pow.exponant, x)
            && !pow.exponant.symbols().is_empty())
        .then(|| ((*pow.base).clone(), (**pow.exponant).clone()))
    })
}

/// The factor `{$B^E$}` of `body` depending on `x`, with `E` depending on `k`, as `(C, B, E)` with `{$C B^E$}` =
/// `body` and `C` free of `x`.
fn power_of(body: &Expr, x: Symbol) -> Option<(Expr, Expr, Expr)> {
    let factors: Vec<&Expr> = match body {
        Term::Mul(mul) => mul.iter().collect(),
        _ => vec![body],
    };
    let mut dependent = factors.iter().filter(|f| depends(f, x));
    let (Some(Term::Pow(pow)), None) = (dependent.next(), dependent.next()) else {
        return None;
    };
    let c = match body {
        Term::Mul(mul) => mul
            .iter()
            .filter(|f| !depends(f, x))
            .fold(value(mul.coefficient.clone()), |res, f| res * f),
        _ => one(),
    };
    if depends(&pow.exponant, x) {
        return None;
    }
    Some((c, (*pow.base).clone(), (**pow.exponant).clone()))
}

/// `{$(alpha, beta)$}` with `{$e = alpha k + beta$}` for rationals `alpha` and `beta`.
fn affine(e: &Expr, k: Symbol) -> Option<(Rational, Rational)> {
    let at = |n: i64| match subs(e, k, &value(Rational::from(n))) {
        Term::Value(c) => Some(c.value),
        _ => None,
    };
    let beta = at(0)?;
    let alpha = at(1)? - &beta;
    (e - &(value(beta.clone()) + value(alpha.clone()) * variable(k)))
        .expand()
        .is_zero()
        .then_some((alpha, beta))
}

/// The held sum `{$sum_(k = a)^oo f$}` of a series in `x` tidied: indexed by the exponent of its power `{$B^E$}` of
/// `x` when `{$E = plus.minus k + c$}` for an integer `c`, its leading zero terms dropped, its general term tidied
/// ([`tidy_term`]). So `{$sum_(k >= 0) k x^(k - 1) / k!$}` is `{$sum_(k >= 0) x^k / k!$}`.
fn tidy_held_sum(body: &Expr, k: Symbol, a: &Expr, x: Symbol) -> Expr {
    let _guard = integer_index(k);
    let (mut body, mut a) = (body.clone(), a.clone());
    if let Some((_, _, e)) = power_of(&body, x)
        && let Some((s, c)) = affine(&e, k)
        && (s == 1 || s == -1)
        && c != 0u32
        && c.denominator_ref() == &1u32
    {
        // The index `{$j = k + s c$}`, whose exponent is `{$s j$}`
        let shift = value(s * c);
        body = subs(&body, k, &(variable(k) - &shift));
        a = &a + &shift;
    }
    for _ in 0..MAX_ZERO_TERMS {
        if !subs(&body, k, &a).expand().is_zero() {
            break;
        }
        a = &a + &one();
    }
    held_sum(tidy_term(&body, k), k, a)
}

/// `{$sum_(k = a)^oo f$}`, not evaluated.
fn held_sum(f: Expr, k: Symbol, a: Expr) -> Expr {
    let oo = variable(Context::OO);
    Term::Fun(Box::new(Fun::new(
        Context::held_sum(),
        vec![f, variable(k), a, oo],
        R,
    )))
    .normalize()
}

/// The recurrence `{$P(n) c_(n + m) = Q(n) c_n$}` of least period and degree satisfied by the coefficients
/// from [`START`] on, with `P` monic, and the least index from which it holds.
fn guess(c: &[Elem]) -> Option<Recurrence> {
    for total in 1..=MAX_PERIOD + MAX_DEGREE {
        for m in 1..=total.min(MAX_PERIOD) {
            let d = total - m;
            if d > MAX_DEGREE {
                continue;
            }
            if let Some(recurrence) = guess_with(c, m, d) {
                return Some(recurrence);
            }
        }
    }
    None
}

/// `{$n^i$}` as an element.
fn power(n: usize, i: usize) -> Elem {
    Elem::rational(Rational::from(n as u64).pow(i as u64))
}

/// The recurrence of period `m` with `P` of degree `d`, if there is exactly one.
fn guess_with(c: &[Elem], m: usize, d: usize) -> Option<Recurrence> {
    // Unknowns `{$p_0, ..., p_(d - 1), q_0, ..., q_d$}`, `{$p_d = 1$}`
    let unknowns = 2 * d + 1;
    let rows: Vec<Vec<Elem>> = (START..c.len().checked_sub(m)?)
        .filter(|&n| !c[n].is_zero() || !c[n + m].is_zero())
        .map(|n| {
            let mut row: Vec<Elem> = (0..d).map(|i| power(n, i).times(&c[n + m])).collect();
            row.extend((0..=d).map(|i| power(n, i).times(&c[n]).negate()));
            row.push(power(n, d).times(&c[n + m]).negate());
            row
        })
        .collect();
    if rows.len() < unknowns + CHECKS {
        return None;
    }
    if !consistent_at_sample(&rows, unknowns) {
        return None;
    }
    let solution = solve_linear_unique(rows, unknowns)?;
    let mut p: Vec<Elem> = solution[..d].to_vec();
    p.push(Elem::one());
    let p = EPoly::new(p);
    let q = EPoly::new(solution[d..].to_vec());
    if q.is_zero() {
        return None;
    }
    let holds =
        |n: usize| p.eval(&power(n, 1)).times(&c[n + m]) == q.eval(&power(n, 1)).times(&c[n]);
    let start = (0..START)
        .rev()
        .take_while(|&n| holds(n))
        .last()
        .unwrap_or(START);
    // `{$P(n) != 0$}` for `{$n >= s$}`, so that the recurrence gives every coefficient
    #[allow(clippy::option_if_let_else)]
    let bound = match p
        .coefficients()
        .iter()
        .map(Elem::as_rational)
        .collect::<Option<Vec<_>>>()
    {
        // Cauchy's bound on the roots
        Some(coefficients) => {
            coefficients
                .iter()
                .map(|c| (*c).abs())
                .fold(Rational::ZERO, |max, c| if c > max { c } else { max })
                + Rational::from(1)
        }
        None => Rational::from(c.len()),
    };
    if bound > MAX_ROOT {
        return None;
    }
    let bound = usize::try_from(&Integer::rounding_from(bound, RoundingMode::Ceiling).0).ok()?;
    if (start..=bound.max(c.len())).any(|n| p.eval(&power(n, 1)).is_zero()) {
        return None;
    }
    Some(Recurrence {
        period: m,
        start,
        p,
        q,
    })
}

/// Whether the system `rows` over `{$QQ(t_1, ..., t_n)$}` may have a solution, by solving it over ℚ at a sample
/// point first, which is much faster when it has none (sums of functions without a common recurrence). A solution
/// gives one at the point, unless one of its denominators vanishes there.
fn consistent_at_sample(rows: &[Vec<Elem>], unknowns: usize) -> bool {
    let levels = rows.iter().flatten().map(Elem::level).max().unwrap_or(0);
    if levels == 0 {
        return true;
    }
    let point = sample_points(levels)
        .next()
        .expect("There are infinitely many points");
    let Some(specialized) = rows
        .iter()
        .map(|row| {
            row.iter()
                .map(|e| e.eval(&point))
                .collect::<Option<Vec<_>>>()
        })
        .collect::<Option<Vec<_>>>()
    else {
        return true;
    };
    solve_linear(specialized, unknowns).is_some()
}

/// The general term tidied: powers of values split ([`split_powers`]), factorials merged, also with the
/// duplication formula, and denominators of linear factors cleared ([`clear_denominators`]).
fn tidy_term(term: &Expr, k: Symbol) -> Expr {
    let term = combine_factorials(&split_powers(term, k));
    let term = combine_factorials(&split_powers(&half_gammas(&duplicate_gammas(&term)), k));
    factor_denominators(&tidy(&merge_powers(
        &absorb_coefficients(&clear_denominators(&binomials(&term, k))),
        k,
    )))
}

/// Sums raised to negative integer powers factored, like `{$1/(k! + 2k k!) = 1/((2k + 1) k!)$}`.
fn factor_denominators(term: &Expr) -> Expr {
    map_tree(term, &|t| {
        let Term::Pow(pow) = t else { return None };
        let (Term::Add(_), Term::Value(e)) = (&*pow.base, &**pow.exponant) else {
            return None;
        };
        if e.value >= 0u32 || e.value.denominator_ref() != &1u32 {
            return None;
        }
        let factored = pow.base.factor();
        (size(&factored) <= size(&pow.base) + 2).then(|| factored.pow(&pow.exponant))
    })
}

/// Powers of values whose exponent is a multiple of `k` merged into a power of a larger value, like
/// `{$2^(2k + 1) = 2 dot 4^k$}` and `{$3^(-2k) = 9^(-k)$}`.
fn merge_powers(term: &Expr, k: Symbol) -> Expr {
    map_tree(term, &|t| {
        let Term::Pow(pow) = t else { return None };
        let Term::Value(base) = &*pow.base else {
            return None;
        };
        let exponent = &**pow.exponant;
        if base.value == 0
            || base.value == 1
            || base.value == -1
            || !is_integer_exponent(exponent, k)
        {
            return None;
        }
        let at = |n: i64| match subs(exponent, k, &value(Rational::from(n))) {
            Term::Value(c) => Some(c.value),
            _ => None,
        };
        let s = at(0)?;
        let r = Integer::try_from(at(1)? - &s).ok()?;
        let r_abs = i64::try_from(&(&r).abs()).ok()?;
        if r_abs < 2 {
            return None;
        }
        let s = i64::try_from(&Integer::try_from(s).ok()?).ok()?;
        let sign = if r > 0 { one() } else { -one() };
        Some(
            value((&base.value).pow(r_abs)).pow(&(sign * variable(k)))
                * value((&base.value).pow(s)),
        )
    })
}

/// Whether the exponent is an integer for every integer `k`: `{$c_0 + c_1 k$}` with integers `{$c_0, c_1$}`.
fn is_integer_exponent(e: &Expr, k: Symbol) -> bool {
    let at = |n: i64| subs(e, k, &value(Rational::from(n)));
    match (at(0), at(1)) {
        (Term::Value(c0), Term::Value(c1)) => {
            let c1 = &c1.value - &c0.value;
            c0.value.denominator_ref() == &1u32
                && c1.denominator_ref() == &1u32
                && (e - &(value(c0.value) + value(c1) * variable(k)))
                    .expand()
                    .is_zero()
        }
        _ => false,
    }
}

/// `{$Gamma(k + b) / (Gamma(b) k!) = (-1)^k binom(-b, k)$}` in products, for `b` free of `k`.
fn binomials(term: &Expr, k: Symbol) -> Expr {
    let Ok(term) = try_map_operands::<Infallible>(term, |t| Ok(binomials(t, k)));
    let Term::Mul(mul) = &term else {
        return term;
    };
    let factors: Vec<&Expr> = mul.iter().collect();
    let inverse = |t: &Expr| match t {
        Term::Pow(pow) if **pow.exponant == value(Rational::from(-1)) => Some((*pow.base).clone()),
        _ => None,
    };
    let find = |f: &dyn Fn(&Expr) -> bool| factors.iter().position(|t| f(t));
    let Some(i) = find(&|t| matches!(unary(t), Some((Context::GAMMA, u)) if depends(u, k))) else {
        return term;
    };
    let Some((_, u)) = unary(factors[i]) else {
        return term;
    };
    let b = (u - &variable(k)).expand();
    if depends(&b, k) {
        return term;
    }
    let gamma_b = fun(Context::GAMMA, b.clone());
    let factorial_k = fun(Context::FACTORIAL, variable(k));
    let (Some(j), Some(l)) = (
        find(&|t| inverse(t).as_ref() == Some(&gamma_b)),
        find(&|t| inverse(t).as_ref() == Some(&factorial_k)),
    ) else {
        return term;
    };
    let binomial = Term::Fun(Box::new(Fun::new(
        Context::BINOMIAL,
        vec![-b, variable(k)],
        R,
    )))
    .normalize();
    factors
        .iter()
        .enumerate()
        .filter(|(index, _)| ![i, j, l].contains(index))
        .fold(value(mul.coefficient.clone()), |res, (_, t)| res * *t)
        * value(Rational::from(-1)).pow(&variable(k))
        * binomial
}

/// `{$Gamma(z + 1/2) = (2z)! sqrt(pi) / (4^z z!)$}` for a non-constant `z` with an integer constant part, so that
/// the general terms are written with factorials, like `{$binom(2k, k) / 4^k$}`.
fn half_gammas(term: &Expr) -> Expr {
    map_tree(term, &|t| {
        let (Context::GAMMA, u) = unary(t)? else {
            return None;
        };
        if matches!(u, Term::Value(_)) {
            return None;
        }
        let z = (u - &value(Rational::from_signeds(1, 2))).expand();
        let constant = constant_part(&z);
        if constant.denominator_ref() != &1u32 {
            return None;
        }
        // `{$Gamma(z + 1/2) = Gamma(z + r + 1/2) / ((z + 1/2) ... (z + r - 1/2))$}`, so that the factorials are
        // of non-negative arguments for `{$k >= 0$}`
        let r = if constant < 0 {
            u64::try_from(&-constant).ok()?
        } else {
            0
        };
        let factors = (0..r).fold(one(), |res, i| res * (u + &value(Rational::from(i))));
        let z = (&z + &value(Rational::from(r))).expand();
        let two_z = (&value(Rational::from(2)) * &z).expand();
        Some(
            fun(Context::FACTORIAL, two_z)
                * variable(Context::PI).pow(&value(Rational::from_signeds(1, 2)))
                / (value(Rational::from(4)).pow(&z) * fun(Context::FACTORIAL, z) * factors),
        )
    })
}

/// The constant term of a sum.
fn constant_part(term: &Expr) -> Rational {
    match term {
        Term::Value(v) => v.value.clone(),
        Term::Add(add) => add
            .iter()
            .find_map(|t| match t {
                Term::Value(v) => Some(v.value.clone()),
                _ => None,
            })
            .unwrap_or_default(),
        _ => Rational::ZERO,
    }
}

/// Powers of values with a symbolic exponent written with the smallest bases, so that they merge:
/// `{$(-2)^k = (-1)^k 2^k$}`, `{$4^k = 2^(2k)$}`, `{$(2/3)^k = 2^k 3^(-k)$}`.
fn split_powers(term: &Expr, k: Symbol) -> Expr {
    map_tree(term, &|t| {
        let Term::Pow(pow) = t else { return None };
        let exponent = &**pow.exponant;
        if matches!(exponent, Term::Value(_)) {
            return None;
        }
        if is_integer_exponent(exponent, k) {
            // `{$(u v)^n = u^n v^n$}` and `{$(u^r)^n = u^(r n)$}` for integers `n` and `r`
            match &*pow.base {
                Term::Mul(mul) if mul.coefficient != 1 || mul.len() > 1 => {
                    let split = |b: &Expr| split_powers(&b.pow(exponent), k);
                    return Some(
                        mul.iter()
                            .fold(split(&value(mul.coefficient.clone())), |res, b| {
                                res * split(b)
                            }),
                    );
                }
                Term::Pow(inner) => {
                    if let Term::Value(r) = &**inner.exponant
                        && r.value.denominator_ref() == &1u32
                    {
                        return Some(split_powers(
                            &inner.base.pow(&(&**inner.exponant * exponent)),
                            k,
                        ));
                    }
                }
                _ => {}
            }
        }
        let Term::Value(base) = &*pow.base else {
            return None;
        };
        if base.value == -1 || base.value == 0 || base.value == 1 {
            return None;
        }
        let exponent = split_powers(exponent, k);
        let sign = if base.value < 0 {
            value(Rational::from(-1)).pow(&exponent)
        } else {
            one()
        };
        let abs = base.value.clone().abs();
        let (num, den) = abs.into_numerator_and_denominator();
        let root = |n: Natural| -> Expr {
            // `{$n = p^r$}` with the largest `r`
            let n_term = value(Rational::from(n.clone()));
            for r in (2..=n.significant_bits()).rev() {
                let p = (&n).floor_root(r);
                if (&p).pow(r) == n {
                    return value(Rational::from(p)).pow(&(value(Rational::from(r)) * &exponent));
                }
            }
            n_term.pow(&exponent)
        };
        Some(sign * root(num) / root(den))
    })
}

/// The coefficient of products absorbed by a power of a value with a symbolic exponent when it is a power of
/// that value, like `{$2^(2k + 2) / 4 = 2^(2k)$}` and `{$2 dot 2^k = 2^(k + 1)$}`.
fn absorb_coefficients(term: &Expr) -> Expr {
    let Ok(term) = try_map_operands::<Infallible>(term, |t| Ok(absorb_coefficients(t)));
    let Term::Mul(mul) = &term else {
        return term;
    };
    let (num, den) = mul
        .coefficient
        .clone()
        .abs()
        .into_numerator_and_denominator();
    let sign = if mul.coefficient < 0 { -one() } else { one() };
    for factor in mul {
        let Term::Pow(pow) = factor else { continue };
        let Term::Value(base) = &*pow.base else {
            continue;
        };
        if matches!(&**pow.exponant, Term::Value(_)) || base.value <= 1 {
            continue;
        }
        let Ok(b) = Natural::try_from(&base.value) else {
            continue;
        };
        // `{$c = b^r$}`
        let log = |mut n: Natural| -> Option<i64> {
            let mut r = 0;
            while n > 1u32 {
                if &n % &b != 0u32 {
                    return None;
                }
                n /= &b;
                r += 1;
            }
            Some(r)
        };
        let (Some(p), Some(q)) = (log(num.clone()), log(den.clone())) else {
            continue;
        };
        if p == 0 && q == 0 {
            continue;
        }
        let rest = mul
            .iter()
            .filter(|t| !std::ptr::eq(*t, factor))
            .fold(sign, |res, t| res * t);
        return rest
            * pow
                .base
                .pow(&(&**pow.exponant + &value(Rational::from(p - q))));
    }
    term
}

/// Factors `{$u^e$}` of products, with `u` a sum of terms with rational coefficients and `e` an integer, written
/// with integer coefficients: `{$1/(2 (k + 1/2)) = 1/(2k + 1)$}`.
fn clear_denominators(term: &Expr) -> Expr {
    map_tree(term, &|t| {
        let Term::Pow(pow) = t else { return None };
        let (Term::Add(add), Term::Value(e)) = (&*pow.base, &**pow.exponant) else {
            return None;
        };
        if e.value.denominator_ref() != &1u32 {
            return None;
        }
        let d = add.iter().fold(Natural::from(1u32), |d, t| match t {
            Term::Value(v) => d.lcm(v.value.denominator_ref()),
            Term::Mul(mul) => d.lcm(mul.coefficient.denominator_ref()),
            _ => d,
        });
        if d == 1u32 {
            return None;
        }
        let d = value(Rational::from(d));
        let base = (&d * &*pow.base).expand();
        Some(base.pow(&pow.exponant) / d.pow(&pow.exponant))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        parse,
        printer::{Print, PrintOptions},
        symbol,
    };

    /// The held sums with their first terms only, `{$sum_(k = a)^(a + 24)$}`.
    fn partial(term: &Expr) -> Expr {
        map_tree(term, &|t| match t {
            Term::Fun(fun) if fun.get_ident() == Context::held_sum() => {
                let [body, k, a, _] = fun.get_args::<Real>()?.as_slice() else {
                    return None;
                };
                let b = a + &value(Rational::from(24));
                let args = vec![body.clone(), k.clone(), a.clone(), b];
                Some(Term::Fun(Box::new(Fun::new(Context::SUM, args, R))).normalize())
            }
            _ => None,
        })
    }

    /// The whole series of `f` agrees with its truncated series.
    #[test]
    fn whole_series_agree_with_truncated_series() {
        let x = symbol!("x");
        let order = Rational::from(8);
        for (f, point) in [
            ("exp(x)", "0"),
            ("sin(x)", "0"),
            ("cos(2*x)", "0"),
            ("asin(x)", "0"),
            ("atan(x)", "0"),
            ("erf(x)", "0"),
            ("ln(1 + x)", "0"),
            ("sqrt(1 + x)", "0"),
            ("(1 + x)^(1/3)", "0"),
            ("1/(1 - x)^3", "0"),
            ("1/(1 + x + x^2)", "0"),
            ("1/((1 - x)*(1 - 2*x))", "0"),
            ("exp(x)*sin(x)", "0"),
            ("exp(x) - 1 - x", "0"),
            ("exp(x)", "1"),
            ("ln(x)", "1"),
            ("exp(x)/x^2", "0"),
            ("1/(x + 1)", "-oo"),
            ("exp(1/x)", "oo"),
            // Proven by the recurrence, the guess failing on the whole
            ("exp(x) + x^40", "0"),
            ("cos(x)^2", "0"),
            // Irrational poles
            ("1/(1 - x - x^2)", "0"),
            ("(x^3 + 1)/(1 - x - x^2)", "0"),
            ("1/(x^2 - x - 1)", "oo"),
            ("1/(1 - 2*x - x^2)", "0"),
            // Bernoulli and Euler numbers
            ("tan(x)", "0"),
            ("1/cos(x)", "0"),
            ("x/(exp(x) - 1)", "0"),
            ("cot(x)", "0"),
            ("tanh(2*x)", "0"),
        ] {
            let (f, point) = (parse!(f, R), parse!(point, R));
            let whole = f.infinite_series(x, &point, Direction::Both).unwrap();
            let truncated = f.series(x, &point, &order, Direction::Both).unwrap();
            let rebuilt = partial(&whole)
                .series(x, &point, &order, Direction::Both)
                .unwrap();
            assert!(
                (&rebuilt - &truncated).expand().is_zero(),
                "{f}: {whole} gives {rebuilt}, not {truncated}"
            );
        }
    }

    /// The whole series of rational functions with complex poles agree numerically with their truncated series,
    /// `{$cos(n theta)$}` not being reduced for most `{$theta$}`.
    #[test]
    fn complex_poles_agree_with_truncated_series() {
        let x = symbol!("x");
        let order = Rational::from(8);
        let point = parse!("0", R);
        for f in [
            "1/(1 - x + 2*x^2)",
            "1/((1 - 2*x)*(1 + x + 2*x^2))",
            "(x^3 + 2)/(3 + x^2 - x)",
        ] {
            let f = parse!(f, R);
            let whole = f.infinite_series(x, &point, Direction::Both).unwrap();
            let truncated = f.series(x, &point, &order, Direction::Both).unwrap();
            let rebuilt = partial(&whole)
                .series(x, &point, &order, Direction::Both)
                .unwrap();
            // Below `{$x^8$}`, at `{$x = 1/10$}`
            let difference = subs(&(&rebuilt - &truncated), x, &parse!("1/10", R));
            let error = approx::approximate(&difference, 15).unwrap();
            assert!(
                error.abs() < Rational::from_signeds(1, 1_000_000_000_000_i64),
                "{f}: {whole} gives {rebuilt}, not {truncated}"
            );
        }
    }

    /// The coefficients computed from the recurrence agree with those of the series engine.
    #[test]
    fn holonomic_coefficients_agree_with_series() {
        let x = symbol!("x");
        for (f, point) in [
            ("exp(x)*sin(x)", "0"),
            ("asin(x) + 1/(1 - x)", "0"),
            ("(1 + x)^(1/3)*exp(x)", "0"),
            ("cos(x)/x^3", "0"),
            ("ln(x)", "2"),
            ("atan(x)", "oo"),
        ] {
            let (f, point) = (parse!(f, R), parse!(point, R));
            let (found, _) = holonomic_coefficients(&f, x, &point, Direction::Both)
                .unwrap()
                .unwrap_or_else(|| panic!("{f}"));
            let order = &found.e0 + Rational::from(20);
            let series = series_terms(&f, x, &point, &order, Direction::Both).unwrap();
            for j in 0..20 {
                let exponent = &found.e0 + Rational::from(j);
                let expected = series
                    .terms
                    .iter()
                    .find(|(e, _)| *e == exponent)
                    .map_or_else(zero, |(_, c)| c.clone());
                assert!(
                    (&found.values[j] - &expected).expand().is_zero(),
                    "{f}: c_{j} = {}, not {expected}",
                    found.values[j]
                );
            }
        }
    }

    /// The differential equation check of the fallback rejects a wrong recurrence.
    #[test]
    fn wrong_guess_rejected() {
        let x = symbol!("x");
        let (f, point) = (parse!("sqrt(x)*exp(x)", R), parse!("0", R));
        let Ok(Ok(found)) = coefficients(&f, x, &point, Direction::Right) else {
            panic!("coefficients");
        };
        // `{$(n + 1) c_(n + 1) = c_n$}` holds, `{$(n + 2) c_(n + 1) = c_n$}` doesn't
        let recurrence = |p: i64| Recurrence {
            period: 1,
            start: 0,
            p: EPoly::new(vec![Elem::integer(p), Elem::one()]),
            q: EPoly::one(),
        };
        assert!(verify_by_ode(
            &f,
            x,
            &point,
            Direction::Right,
            &found,
            &recurrence(1)
        ));
        assert!(!verify_by_ode(
            &f,
            x,
            &point,
            Direction::Right,
            &found,
            &recurrence(2)
        ));
    }

    #[test]
    fn puiseux_series() {
        let x = symbol!("x");
        let f = parse!("sqrt(x)*exp(x)", R);
        let whole = f
            .infinite_series(x, &parse!("0", R), Direction::Right)
            .unwrap();
        let typst = whole.with_options(PrintOptions::typst()).to_string();
        assert_eq!(typst, "sum_(k = 0)^(oo) frac(x^(k+frac(1, 2)), k!)");
    }
}
