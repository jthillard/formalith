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
            arithmetic::traits::{Abs, FloorRoot, Gcd, Lcm, Pow},
            basic::traits::Zero,
            conversion::traits::RoundingFrom,
            logic::traits::SignificantBits,
        },
        rounding_modes::RoundingMode,
    },
};

use std::convert::Infallible;

use crate::{
    context::{Context, Symbol},
    field::real::{
        R, approx,
        expr::{
            Expr, Real, depends, fun, infinity_sign, map_tree, one, size, subs, try_map_operands,
            unary, value, variable, zero,
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
    super::holonomic,
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
    let res = split_series(f, x, point, direction, k, split);
    if res.is_err() && split && is_rational_function(f) && f.symbols().len() == 1 {
        return rational_series(f, x, point, direction, k).or(res);
    }
    res
}

/// The series of `f` from the partial fractions over the real roots of its denominator, which must be simple:
/// `{$A / (w - r)$}` gives `{$-A r^(-n - 1)$}` for the coefficient of `{$w^n$}`, `{$A = N(r) / D'(r)$}`. For
/// rational functions with rational coefficients whose irreducible factors aren't linear, like
/// `{$1 / (1 - x - x^2)$}`, whose coefficients satisfy a recurrence with constant coefficients (no two-term one).
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
    let wv = variable(w);
    let term = |p: &Poly| {
        p.coefficients()
            .iter()
            .enumerate()
            .fold(zero(), |res, (i, c)| {
                res + value(c.clone()) * wv.pow(&value(Rational::from(i)))
            })
    };
    // `{$D(w) = d_0 product_i (1 - rho_i w)$}`, the `{$rho_i$}` being the roots of the reversed polynomial
    let reversed = Poly::new(den.coefficients().iter().rev().cloned().collect());
    let roots = eigen::real_roots(&term(&reversed), w).ok_or(LimitError::Unsupported)?;
    if roots.len() != den.degree() || roots.iter().any(|(_, m)| *m != 1) {
        return Err(LimitError::Unsupported);
    }
    let (rest, derivative) = (term(&rest), term(&den.derivative()));
    let n = variable(k);
    // `{$A / (w - r) = -A rho / (1 - rho w)$}` with `{$r = 1 / rho$}` and `{$A = N(r) / D'(r)$}`
    let mut general = zero();
    for (rho, _) in &roots {
        let r = (one() / rho.clone()).simplify();
        let at = |p: &Expr| p.substitute(w, &r).map(|t| t.expand());
        let a = at(&rest).ok_or(LimitError::Unsupported)?
            / at(&derivative).ok_or(LimitError::Unsupported)?;
        let b = rationalize(&(-(a * rho)).simplify());
        general += b * rho.pow(&n);
    }
    // `w` in terms of `x`
    let back = match infinity_sign(point) {
        Some(sign) => value(Rational::from(sign as i64)) / variable(x),
        None if direction == Direction::Left => point - &variable(x),
        None => variable(x) - point.clone(),
    };
    // The first coefficients, with the polynomial part, then the general term
    let _guard = integer_index(k);
    let first = quotient.coefficients().len();
    let mut res = zero();
    for (i, c) in quotient.coefficients().iter().enumerate() {
        let i_term = value(Rational::from(i));
        let c = (value(c.clone()) + subs(&general, k, &i_term)).simplify();
        res += c * w_power(&back, &i_term);
    }
    let general = tidy(&(general * w_power(&back, &n)));
    Ok(res + held_sum(general, k, value(Rational::from(first))))
}

/// A fraction whose denominator is `{$a + b sqrt(c)$}` (rational `a`, `b`, `c`), multiplied by the conjugate
/// `{$a - b sqrt(c)$}` above and below, like `{$(sqrt(5) + 3) / (sqrt(5) + 5) = (sqrt(5) + 5) / 10$}`.
fn rationalize(term: &Expr) -> Expr {
    let (num, den) = term.as_fraction(true);
    let Term::Add(add) = &den else {
        return term.clone();
    };
    let is_radical = |t: &Expr| match t {
        Term::Pow(pow) => {
            matches!(&*pow.base, Term::Value(_))
                && **pow.exponant == value(Rational::from_signeds(1, 2))
        }
        Term::Mul(mul) => mul.iter().count() == 1 && mul.iter().all(|f| matches!(f, Term::Pow(_))),
        _ => false,
    };
    let terms: Vec<&Expr> = add.iter().collect();
    let [a, b] = terms.as_slice() else {
        return term.clone();
    };
    let (rational, radical) = match (a, b) {
        (Term::Value(_), r) if is_radical(r) => (*a, *b),
        (r, Term::Value(_)) if is_radical(r) => (*b, *a),
        _ => return term.clone(),
    };
    let conjugate = rational - radical;
    let den = (&den * &conjugate).expand();
    if !matches!(den, Term::Value(_)) {
        return term.clone();
    }
    let num = (num * conjugate).expand();
    // The content of the numerator out, `{$(2 sqrt(5) + 10) / 20 = (sqrt(5) + 5) / 10$}`
    let Term::Add(add) = &num else {
        return num / den;
    };
    let content = add.iter().try_fold(Natural::from(0u32), |g, t| {
        let c = match t {
            Term::Value(v) => &v.value,
            Term::Mul(mul) => &mul.coefficient,
            _ => return None,
        };
        (c.denominator_ref() == &1u32).then(|| g.gcd(c.numerator_ref()))
    });
    match content {
        Some(g) if g > 1u32 => {
            let g = value(Rational::from(g));
            (&num / &g).expand() * (g / den)
        }
        _ => num / den,
    }
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
            .find(|[other, j, b]| j == k && b == a && !depends(&(body / other).simplify(), x))
        {
            Some([other, _, _]) => *other = &*other + body,
            None => sums.push([body.clone(), k.clone(), a.clone()]),
        }
    }
    sums.into_iter().fold(res, |res, [body, k, a]| {
        let Term::Symbol(k) = k else { unreachable!() };
        res + held_sum(tidy_term(&body, k.symbol), k.symbol, a)
    })
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
/// points, then proven zero by expansion or simplification. Undecided expressions aren't zero.
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
    e.expand().is_zero()
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
    tidy(&merge_powers(
        &absorb_coefficients(&clear_denominators(&binomials(&term, k))),
        k,
    ))
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
