//! Zeilberger's algorithm (creative telescoping, Petkovšek, Wilf, Zeilberger, *A = B*, chapter 6): definite sums
//! `{$S(n) = sum_(k = a)^(s n + c) F(n, k)$}` of a term `F` hypergeometric in `n` and `k`, which Gosper's algorithm
//! can't sum indefinitely, like `{$sum_(k = 0)^n binom(n, k)^2 = binom(2n, n)$}`.
//!
//! For increasing orders `J` (at most 2), it looks for `{$sigma_0(n), ..., sigma_J(n) = 1$}` and a certificate `G = R F`, `R`
//! rational, with `{$sum_j sigma_j F(n + j, k) = G(n, k + 1) - G(n, k)$}`: Gosper's algorithm on the left side, its
//! unknowns `{$sigma_j$}` solved with those of the key equation. Summing over `k` gives a recurrence
//! `{$sum_j sigma_j S(n + j) = "rhs"(n)$}`, the right side made of the boundary terms. Recurrences of order 1 are
//! solved with a product (and a sum when the right side isn't zero), homogeneous ones of higher order with rational
//! coefficients by their hypergeometric solutions (see [`holonomic::hyper`]), fitted on values computed term by term.
//! The closed form, valid for `{$n >= n_0$}` past the singular indices, is checked against such values, and the
//! values below `{$n_0$}` it doesn't give are cases of a `piecewise`.

// Orders, degrees and indices are small
#![allow(clippy::cast_possible_wrap)]

use std::convert::Infallible;

use malachite::{Rational, base::num::arithmetic::traits::Abs};

use crate::{
    context::{Context, Symbol},
    field::real::{
        R, approx,
        expr::{
            Expr, Real, depends, map_tree, one, size, subs, try_map_operands, unary, value,
            variable, zero,
        },
    },
    holonomic::{
        self,
        ore::{Kind, Operator},
        ratfun::{RatFun, natural_roots},
        recurrence::Recurrence,
    },
    polynom::{
        dense::Coefficient,
        fraction::{EPoly, Elem, sample_points, solve_linear},
    },
    term::{Expand, Fun, Normalize, Term, flags::Flags, relation::Relation},
};

use super::{
    at,
    field::{Params, reduce},
    gosper, integer_index, is_rational_function,
    product::combine_factorials,
    taylor::{hypergeometric_combination, tidy_term},
};

/// Largest order of the recurrence.
const MAX_ORDER: usize = 2;
/// Largest degree of the polynomial of the key equation.
const MAX_DEGREE: usize = 40;
/// Largest index from which the closed form holds.
const MAX_START: usize = 50;
/// Largest number of values below the index from which the closed form holds which it doesn't give, written as
/// cases of a `piecewise`.
const MAX_EXCEPTIONS: usize = 3;
/// Values where the closed form is checked, and equations checking the fit of hypergeometric solutions.
const CHECKS: usize = 3;

/// The sum `{$sum_(k = a)^b f$}`, `a` being an integer and `{$b = s n + c$}` with integers `{$s >= 1$}` and `c`, if
/// Zeilberger's algorithm finds it.
pub(super) fn definite(f: &Expr, k: Symbol, a: &Expr, b: &Expr) -> Option<Expr> {
    let Term::Value(start) = a else {
        return None;
    };
    let start = i64::try_from(&start.value).ok()?;
    let (n, slope, offset) = upper_bound(b)?;
    if !depends(f, n) {
        return None;
    }
    if let Term::Add(add) = f {
        // Term by term, each one by its own method
        return add
            .iter()
            .try_fold(zero(), |res, t| Some(res + t.sum(k, a, b).ok()?));
    }
    // Factors free of `k` taken out
    let (outer, summand) = match f {
        Term::Mul(mul) => mul.iter().fold(
            (value(mul.coefficient.clone()), one()),
            |(outer, summand), t| {
                if depends(t, k) {
                    (outer, summand * t)
                } else {
                    (outer * t, summand)
                }
            },
        ),
        _ => (one(), f.clone()),
    };
    let _guard = integer_index(n);
    let mut params = Params::default();
    let telescoper = Telescoper::find(&summand, n, k, &mut params)?;
    let rhs = telescoper.rhs(&summand, k, a, b, start, slope, &mut params)?;
    let rhs = (!rhs.is_zero()).then_some(rhs);
    let sigma: Vec<Expr> = telescoper.sigma.iter().map(|s| params.to_term(s)).collect();
    // From the first `n` whose sum isn't below the empty sum, past the singular indices: poles of the
    // coefficients and of the certificate, zeros of the ratio of a recurrence of order 1
    let first = usize::try_from(((start - 1 - offset).max(0) + slope - 1) / slope).ok()?;
    let mut n0 = first;
    let mut singular = vec![];
    let (r, s) = &telescoper.certificate;
    let coefficients = r.coefficients().iter().chain(s.coefficients());
    for (j, e) in telescoper.sigma.iter().chain(coefficients).enumerate() {
        let (num, den) = Params::default().rational(&params.to_term(e), n)?;
        singular.extend(natural_roots(&den)?);
        if j == 0 && sigma.len() == 2 && !num.is_zero() {
            singular.extend(natural_roots(&num)?);
        }
    }
    for root in singular {
        n0 = n0.max(usize::try_from(root).ok()? + 1);
    }
    if n0 > MAX_START {
        return None;
    }
    let values = |m: usize| direct(&summand, n, k, a, b, m);
    let (res, checked_from) = if sigma.len() == 2 {
        first_order(&sigma[0], rhs.as_ref(), n, n0, &values)?
    } else {
        (higher_order(&sigma, rhs.as_ref(), n, n0, &values)?, n0)
    };
    // The closed form against values term by term
    let agrees = |res: &Expr, m: usize, direct: &Expr| {
        let at_m = combine_factorials(&subs(res, n, &value(Rational::from(m))));
        let difference = polynomial_binomials(&(at_m - direct)).expand();
        difference.is_zero() || negligible(&difference)
    };
    for m in checked_from..checked_from + CHECKS {
        if !agrees(&res, m, &values(m)?) {
            return None;
        }
    }
    let res = outer.clone() * simplify_powers(&binomials(&tidy_term(&binomials(&res), n)), n);
    // The values below `{$n_0$}` which the closed form doesn't give, as cases
    let mut exceptions = vec![];
    for m in first..checked_from {
        let direct = subs(&outer, n, &value(Rational::from(m))) * values(m)?;
        if !agrees(&res, m, &direct) {
            exceptions.push((m, direct));
        }
    }
    if exceptions.len() > MAX_EXCEPTIONS {
        return None;
    }
    if exceptions.is_empty() {
        return Some(res);
    }
    let mut args = vec![];
    for (m, direct) in exceptions {
        let mut condition = Term::Fun(Box::new(Fun::new(
            Relation::Equal.symbol(),
            vec![variable(n), value(Rational::from(m))],
            R,
        )));
        condition.set_normalized(true);
        args.extend([condition, direct]);
    }
    args.push(res);
    Some(Term::Fun(Box::new(Fun::new(Context::PIECEWISE, args, R))).normalize())
}

/// Factorials `{$u! / (p! q!)$}` with `{$p + q = u$}` in products written `{$binom(u, p)$}`, `{$Gamma(u + 1)$}` being
/// `{$u!$}`, like `{$(2n)! / n!^2 = binom(2n, n)$}` and `{$Gamma(m + n + 1) / (n! Gamma(m + 1)) = binom(m + n, n)$}`.
fn binomials(term: &Expr) -> Expr {
    let Ok(term) = try_map_operands::<Infallible>(term, |t| Ok(binomials(t)));
    let Term::Mul(mul) = &term else {
        return term;
    };
    // The factorials with their integer exponents and the factor they come from, and the other factors
    let mut factorials: Vec<(Expr, i64, Expr)> = vec![];
    let mut rest = value(mul.coefficient.clone());
    for t in mul {
        let (base, exponent) = match t {
            Term::Pow(pow) => match &**pow.exponant {
                Term::Value(e) => (&*pow.base, i64::try_from(&e.value).ok()),
                _ => (t, None),
            },
            _ => (t, Some(1)),
        };
        match (unary(base), exponent) {
            (Some((Context::FACTORIAL, u)), Some(e)) => {
                factorials.push((u.clone(), e, base.clone()));
            }
            (Some((Context::GAMMA, u)), Some(e)) => {
                factorials.push(((u - &one()).expand(), e, base.clone()));
            }
            _ => rest *= t,
        }
    }
    let mut found = vec![];
    'search: loop {
        for i in (0..factorials.len()).filter(|i| factorials[*i].1 > 0) {
            for j in (0..factorials.len()).filter(|j| factorials[*j].1 < 0) {
                for l in (j..factorials.len()).filter(|l| factorials[*l].1 < -i64::from(*l == j)) {
                    let (u, p, q) = (&factorials[i].0, &factorials[j].0, &factorials[l].0);
                    if (u - &(p + q)).expand().is_zero() {
                        found.push(Term::Fun(Box::new(Fun::new(
                            Context::BINOMIAL,
                            vec![u.clone(), p.clone()],
                            R,
                        ))));
                        factorials[i].1 -= 1;
                        factorials[j].1 += 1;
                        factorials[l].1 += 1;
                        continue 'search;
                    }
                }
            }
        }
        break;
    }
    if found.is_empty() {
        return term;
    }
    factorials.into_iter().fold(rest, |res, (_, e, base)| {
        res * base.pow(&value(Rational::from(e)))
    }) * found.into_iter().fold(one(), |res, t| res * t.normalize())
}

/// The term simplified as a rational function of `n` and of the powers `{$c^(alpha n + beta)$}` of values, written
/// `{$c^beta t^alpha$}` with a new symbol `t` per base, its denominator factored, when it is one and that is smaller.
fn simplify_powers(term: &Expr, n: Symbol) -> Expr {
    let bases = std::cell::RefCell::new(Vec::<(Expr, Symbol)>::new());
    let replaced = map_tree(term, &|t| {
        let Term::Pow(pow) = t else { return None };
        if !matches!(&*pow.base, Term::Value(_)) || !depends(&pow.exponant, n) {
            return None;
        }
        let alpha = gosper::step(&pow.exponant, n)?;
        let Term::Value(a) = &alpha else { return None };
        let alpha = i64::try_from(&a.value).ok()?;
        let beta = (&**pow.exponant - &(&alpha_term(alpha) * &variable(n))).expand();
        let mut bases = bases.borrow_mut();
        let t = if let Some((_, t)) = bases.iter().find(|(b, _)| b == &*pow.base) {
            *t
        } else {
            let t = Symbol::new(format!("@z{}", bases.len()));
            bases.push(((*pow.base).clone(), t));
            t
        };
        Some(pow.base.pow(&beta) * variable(t).pow(&alpha_term(alpha)))
    });
    let bases = bases.into_inner();
    if bases.is_empty() || !is_rational_function(&replaced) {
        return term.clone();
    }
    // The denominator factored
    let (num, den) = replaced.simplify().as_fraction(true);
    let simplified = bases.iter().fold(num / den.factor(), |res, (base, t)| {
        subs(&res, *t, &base.pow(&variable(n)))
    });
    if size(&simplified) < size(term) {
        simplified
    } else {
        term.clone()
    }
}

/// The integer as a term.
fn alpha_term(alpha: i64) -> Expr {
    value(Rational::from(alpha))
}

/// `{$binom(u, d)$}` for a small natural `d` written `{$u (u - 1) ... (u - d + 1) / d!$}`, so that values with
/// parameters compare by expansion.
fn polynomial_binomials(term: &Expr) -> Expr {
    map_tree(term, &|t| {
        let Term::Fun(f) = t else { return None };
        let (Context::BINOMIAL, Some([u, Term::Value(d)])) =
            (f.get_ident(), f.get_args::<Real>().map(Vec::as_slice))
        else {
            return None;
        };
        let d = u64::try_from(&d.value).ok().filter(|d| *d <= 20)?;
        Some((0..d).fold(one(), |res, i| {
            res * (u - &value(Rational::from(i))) / value(Rational::from(i + 1))
        }))
    })
}

/// `{$(n, s, c)$}` with `{$b = s n + c$}`, `n` the only symbol of `b`, `s` and `c` integers and `{$s >= 1$}`.
fn upper_bound(b: &Expr) -> Option<(Symbol, i64, i64)> {
    let symbols: Vec<Symbol> = b
        .symbols()
        .into_iter()
        .filter(|s| !Context::is_builtin_constant(*s))
        .collect();
    let [n] = symbols.as_slice() else {
        return None;
    };
    let Term::Value(slope) = gosper::step(b, *n)? else {
        return None;
    };
    let slope = i64::try_from(&slope.value).ok().filter(|s| *s >= 1)?;
    let Term::Value(offset) = (b - &(value(Rational::from(slope)) * variable(*n))).expand() else {
        return None;
    };
    Some((*n, slope, i64::try_from(&offset.value).ok()?))
}

/// `{$sum_(k = a)^(b(m)) f(m, k)$}` term by term, `None` when it isn't computed.
fn direct(f: &Expr, n: Symbol, k: Symbol, a: &Expr, b: &Expr, m: usize) -> Option<Expr> {
    let m = value(Rational::from(m));
    subs(f, n, &m).sum(k, a, &subs(b, n, &m)).ok()
}

/// Whether a constant is zero up to its approximation, for closed forms with angles like `{$cos(n theta)$}` not
/// reduced at integers.
fn negligible(difference: &Expr) -> bool {
    difference
        .symbols()
        .iter()
        .all(|s| Context::is_builtin_constant(*s))
        && approx::approximate(difference, 30)
            .is_some_and(|d| d.abs() < Rational::from_signeds(1, 1_000_000_000_000_000_000_i64))
}

/// A recurrence `{$sum_j sigma_j F(n + j, k) = G(n, k + 1) - G(n, k)$}` with its certificate `{$G = R F$}`, as
/// fractions in `k` whose coefficients contain `n`.
struct Telescoper {
    /// `{$sigma_0, ..., sigma_J$}`, `{$sigma_J = 1$}`.
    sigma: Vec<Elem>,
    /// The certificate `R`, not reduced, its denominator monic.
    certificate: (EPoly, EPoly),
    /// `{$F(n + j, k) / F(n, k)$}` for `{$j = 0, ..., J$}`.
    shifts: Vec<(EPoly, EPoly)>,
    /// `{$F(n + j, k + 1) / F(n + j, k)$}` for `{$j = 0, ..., J$}`.
    steps: Vec<(EPoly, EPoly)>,
}

impl Telescoper {
    /// The recurrence of least order, if there is one of order at most [`MAX_ORDER`] and `F` is hypergeometric.
    fn find(f: &Expr, n: Symbol, k: Symbol, params: &mut Params) -> Option<Self> {
        let shifted = |j: usize| subs(f, n, &(variable(n) + value(Rational::from(j))));
        let mut shifts = vec![(EPoly::one(), EPoly::one())];
        let mut steps = vec![gosper::ratio(f, k, params)?];
        for order in 1..=MAX_ORDER {
            let (num, den) = gosper::ratio_in(&shifted(order - 1), n, k, params)?;
            let (p, q) = shifts.last()?;
            shifts.push(reduce(&p.mul(&num), &q.mul(&den)));
            steps.push(gosper::ratio(&shifted(order), k, params)?);
            if let Some((sigma, certificate)) = telescope(&steps[0], &shifts, k) {
                return Some(Self {
                    sigma,
                    certificate,
                    shifts,
                    steps,
                });
            }
        }
        None
    }

    /// The right side `{$G(n, b + 1) - G(n, a) + sum_j sigma_j sum_(i = 1)^(s j) F(n + j, b + i)$}` of the recurrence
    /// of the sums `{$sum_(k = a)^b F(n, k)$}`, `{$b = s n + c$}`, `None` at a pole. With
    /// `{$F = F_r F_s$}`, `{$F_r$}` its rational part, every term is a rational function of `k` at `{$k = b$}` times
    /// `{$F_s(n, b)$}`, or at `{$k = a$}` times `{$F_s(n, a)$}`, so that zeros of `{$F_r$}` cancel poles of the certificate.
    #[allow(clippy::too_many_arguments)]
    fn rhs(
        &self,
        f: &Expr,
        k: Symbol,
        a: &Expr,
        b: &Expr,
        start: i64,
        slope: i64,
        params: &mut Params,
    ) -> Option<Expr> {
        let b_elem = params.elem(b)?;
        let (rational, special) = gosper::split_rational(f, k, params);
        let fr = params.rational(&rational, k)?;
        // `{$G(n, b + 1) = R(b + 1) F(n, b + 1) / F(n, b) dot F(n, b)$}`
        let mut upper = product_at(
            &[(&self.certificate, 1), (&self.steps[0], 0), (&fr, 0)],
            &b_elem,
        )?;
        for (j, (sigma, (shift, step))) in self
            .sigma
            .iter()
            .zip(self.shifts.iter().zip(&self.steps))
            .enumerate()
        {
            // `{$F(n + j, b + i) / F(n, b) = F(n + j, b) / F(n, b) product_(l < i) F(n + j, b + l + 1) / F(n + j, b + l)$}`
            let mut factors = vec![(&fr, 0), (shift, 0)];
            for i in 0..usize::try_from(slope).ok()? * j {
                factors.push((step, i as i64));
                upper = upper.plus(&sigma.times(&product_at(&factors, &b_elem)?));
            }
        }
        let lower = product_at(&[(&self.certificate, 0), (&fr, 0)], &Elem::integer(start))?;
        if upper.is_zero() && lower.is_zero() {
            return Some(zero());
        }
        let value_at = |e: &Elem, point: &Expr| -> Option<Expr> {
            if e.is_zero() {
                Some(zero())
            } else {
                Some(params.to_term(e) * at(&special, k, point).ok()?)
            }
        };
        Some((value_at(&upper, b)? - value_at(&lower, a)?).expand())
    }
}

/// The value at `x` of the product of the fractions `{$f_i(k + s_i)$}`, given with their shifts `{$s_i$}`, `None` at a
/// pole. Each one is evaluated, and only when one has a pole is the product formed, the factor `{$k - x$}` being
/// divided out of its numerator and denominator while both vanish at `x` (cheaper than reducing it by a gcd).
fn product_at(factors: &[(&(EPoly, EPoly), i64)], x: &Elem) -> Option<Elem> {
    let mut res = Elem::one();
    for ((num, den), shift) in factors {
        let point = x.plus(&Elem::integer(*shift));
        let den = den.eval(&point);
        if den.is_zero() {
            let (mut num, mut den) = factors.iter().fold(
                (EPoly::one(), EPoly::one()),
                |(p, q), ((num, den), shift)| {
                    let shift = Elem::integer(*shift);
                    (p.mul(&num.shift(&shift)), q.mul(&den.shift(&shift)))
                },
            );
            let linear = EPoly::new(vec![x.negate(), Elem::one()]);
            while den.eval(x).is_zero() {
                if !num.eval(x).is_zero() {
                    return None;
                }
                num = num.exact_div(&linear);
                den = den.exact_div(&linear);
            }
            return Some(num.eval(x).divide(&den.eval(x)));
        }
        res = res.times(&num.eval(&point).divide(&den));
    }
    Some(res)
}

/// `{$sigma_0, ..., sigma_J = 1$}` and the certificate `R` of the recurrence of order `J`, from the ratio
/// `{$F(n, k + 1) / F(n, k)$}` and the shifts `{$F(n + j, k) / F(n, k)$}`, if there is one.
fn telescope(
    step: &(EPoly, EPoly),
    shifts: &[(EPoly, EPoly)],
    k: Symbol,
) -> Option<(Vec<Elem>, (EPoly, EPoly))> {
    let order = shifts.len() - 1;
    // `{$sum_j sigma_j F(n + j, k) = F(n, k) P(k) / Q(k)$}`, `{$P = sum_j sigma_j p_j$}`
    let q = shifts.iter().fold(EPoly::one(), |q, (_, den)| {
        q.mul(den).exact_div(&q.gcd(den))
    });
    let p: Vec<EPoly> = shifts
        .iter()
        .map(|(num, den)| num.mul(&q.exact_div(den)))
        .collect();
    // Gosper form of the ratio of `{$F / Q$}`, `P` going into `c`
    let one = Elem::one();
    let (num, den) = reduce(&step.0.mul(&q), &step.1.mul(&q.shift(&one)));
    let (a, b, c) = gosper::gosper_form(&num, &den, k)?;
    let b = b.shift(&Elem::integer(-1));
    let c_degree = c.degree() + p.iter().map(EPoly::degree).max()?;
    let degree = gosper::degree_bound(&a, &b, c_degree).unwrap_or(0);
    if degree > MAX_DEGREE {
        return None;
    }
    // `{$a(k) x(k + 1) - b(k - 1) x(k) - c(k) sum_(j < J) sigma_j p_j(k) = c(k) p_J(k)$}`
    let mut columns: Vec<EPoly> = (0..=degree)
        .map(|i| {
            let monomial = EPoly::monomial(Elem::one(), i);
            a.mul(&monomial.shift(&one)).sub(&b.mul(&monomial))
        })
        .collect();
    columns.extend(p[..order].iter().map(|p| c.mul(p).neg()));
    let rhs = c.mul(&p[order]);
    let rows_count = columns
        .iter()
        .chain(std::iter::once(&rhs))
        .map(|p| p.coefficients().len())
        .max()?;
    let rows: Vec<Vec<Elem>> = (0..rows_count)
        .map(|row| {
            columns
                .iter()
                .map(|p| p.coefficient(row))
                .chain(std::iter::once(rhs.coefficient(row)))
                .collect()
        })
        .collect();
    if !consistent_at_sample(&rows, columns.len()) {
        return None;
    }
    let solution = solve_linear(rows, columns.len())?;
    let x = EPoly::new(solution[..=degree].to_vec());
    let mut sigma = solution[degree + 1..].to_vec();
    sigma.push(Elem::one());
    // `{$G = b(k - 1) x(k) / c(k) dot F P / Q = b(k - 1) x(k) / (c_0(k) Q(k)) F$}`, `c` being `{$c_0$}` here
    // Not reduced: gcds over `{$QQ(n)$}` blow up, and the fraction is only evaluated
    let den = c.mul(&q);
    let lead = den.leading().inverse();
    let certificate = (b.mul(&x).scale(&lead), den.scale(&lead));
    Some((sigma, certificate))
}

/// Whether the linear system, whose coefficients contain `n` and the parameters, has a solution at a sample point
/// of them, a quick test before solving it in `{$QQ(n, t_1, ...)$}`: a solution there gives one at almost every point.
fn consistent_at_sample(rows: &[Vec<Elem>], unknowns: usize) -> bool {
    let levels = rows.iter().flatten().map(Elem::level).max().unwrap_or(0);
    let Some(specialized) = sample_points(levels).take(8).find_map(|point| {
        rows.iter()
            .map(|row| {
                row.iter()
                    .map(|e| e.eval(&point))
                    .collect::<Option<Vec<_>>>()
            })
            .collect::<Option<Vec<_>>>()
    }) else {
        return true;
    };
    solve_linear(specialized, unknowns).is_some()
}

/// The solution of `{$S(n + 1) + sigma_0(n) S(n) = "rhs"(n)$}` from `{$S(n_0)$}`, and the first index where it holds:
/// `{$S(n) = H(n) (S(n_0) + sum_(m = n_0)^(n - 1) "rhs"(m) / H(m + 1))$}` with `{$H(n) = product_(m = n_0)^(n - 1) (-sigma_0(m))$}`.
fn first_order(
    sigma: &Expr,
    rhs: Option<&Expr>,
    n: Symbol,
    n0: usize,
    values: &impl Fn(usize) -> Option<Expr>,
) -> Option<(Expr, usize)> {
    let m = Symbol::new("@m");
    let start = value(Rational::from(n0));
    let last = variable(n) - one();
    if sigma.is_zero() && rhs.is_none() {
        // `{$S(n) = 0$}` for `{$n > n_0$}`
        return Some((zero(), n0 + 1));
    }
    let rho = subs(&(-sigma).expand(), n, &variable(m));
    let h = rho.product(m, &start, &last).ok()?;
    let s0 = values(n0)?;
    let res = match rhs {
        None => s0 * h,
        Some(rhs) => {
            let term = subs(rhs, n, &variable(m)) / subs(&h, n, &(variable(m) + one()));
            let sum = term.sum(m, &start, &last).ok()?;
            h * (s0 + sum)
        }
    };
    Some((res, n0))
}

/// The solution of the homogeneous recurrence `{$sum_j sigma_j(n) S(n + j) = 0$}` with rational coefficients as a
/// combination of its hypergeometric solutions, fitted on values from `{$n_0$}`.
fn higher_order(
    sigma: &[Expr],
    rhs: Option<&Expr>,
    n: Symbol,
    n0: usize,
    values: &impl Fn(usize) -> Option<Expr>,
) -> Option<Expr> {
    use holonomic::hyper::Gaussian;
    if rhs.is_some() {
        return None;
    }
    // Polynomial coefficients
    let mut fractions = vec![];
    for s in sigma {
        fractions.push(Params::default().rational(s, n)?);
    }
    let lcm = fractions.iter().fold(EPoly::one(), |l, (_, den)| {
        l.mul(den).exact_div(&l.gcd(den))
    });
    let coefficients = fractions
        .iter()
        .map(|(num, den)| RatFun::poly(num.mul(&lcm.exact_div(den))))
        .collect();
    let recurrence = Recurrence {
        operator: Operator::new(Kind::Shift, coefficients)?,
        start: n0,
    };
    let order = recurrence.operator.order();
    let solutions = holonomic::hyper::solutions(&recurrence);
    if solutions.is_empty() {
        return None;
    }
    let n0 = holonomic::hyper::past_roots(&solutions, n0)?;
    if n0 > MAX_START {
        return None;
    }
    // Agreeing on `order` consecutive values proves it, the others check the fit
    let rows = solutions.len().max(order) + CHECKS;
    let equations = (n0..n0 + rows)
        .map(|m| {
            let Term::Value(v) = values(m)? else {
                return None;
            };
            let mut row = solutions
                .iter()
                .map(|s| s.eval(n0, m))
                .collect::<Option<Vec<_>>>()?;
            row.push(Gaussian::from_rational(v.value));
            Some(row)
        })
        .collect::<Option<Vec<_>>>()?;
    let alpha = solve_linear(equations, solutions.len())?;
    hypergeometric_combination(&solutions, &alpha, &variable(n), n0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{field::real::R, parse, symbol};

    /// `{$sigma_0, ..., sigma_J$}` of the recurrence of `f`.
    fn recurrence(f: &str) -> Vec<Expr> {
        let (n, k) = (symbol!("n"), symbol!("k"));
        let mut params = Params::default();
        let telescoper = Telescoper::find(&parse!(f, R), n, k, &mut params).unwrap();
        telescoper.sigma.iter().map(|s| params.to_term(s)).collect()
    }

    #[test]
    fn recurrences() {
        // `{$S(n + 1) = 2 S(n)$}`
        assert_eq!(
            recurrence("binomial(n, k)"),
            vec![parse!("-2", R), parse!("1", R)]
        );
        // `{$(n + 1) S(n + 1) = (4n + 2) S(n)$}`
        assert_eq!(
            recurrence("binomial(n, k)^2"),
            vec![parse!("(-4n - 2)/(n + 1)", R), parse!("1", R)]
        );
    }

    /// `{$S(n + 2) - 5 S(n + 1) + 6 S(n) = 0$}` with `{$S(n) = 2^n + 3^n$}`, by its hypergeometric solutions.
    #[test]
    fn second_order() {
        let n = symbol!("n");
        let sigma = [parse!("6", R), parse!("-5", R), parse!("1", R)];
        let values = |m: usize| Some(parse!(&format!("2^{m} + 3^{m}"), R));
        let res = higher_order(&sigma, None, n, 0, &values).unwrap();
        assert_eq!(res, parse!("2^n + 3^n", R));
    }
}
