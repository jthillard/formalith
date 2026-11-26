//! Real and imaginary parts of complex expressions, so that integrals, limits and series are computed in `{$RR$}`.

use std::cmp::Ordering;

use malachite::{
    Integer, Rational,
    base::num::{
        arithmetic::traits::UnsignedAbs,
        basic::traits::{One, Zero},
    },
};

use super::C;
use crate::{
    context::{Context, Symbol},
    field::{
        Group, Semiring, TryExprFrom,
        real::{
            R,
            expr::{self, Expr, Real, fun, half, one, size, value, variable, zero},
            radicals,
            sign::{SignMode, sign},
        },
    },
    term::{Expand, Fun, Normalize, Term, Value, flags::Flags},
};

/// A complex expression over `{$CC$}`.
type Complex = Term<C<R<Rational>>>;

/// The largest absolute integer exponent expanded by [`split`].
const MAX_EXPONANT: u64 = 16;

/// The parts `{$(u, v)$}` of `{$f = u + i v$}`, assuming every symbol is real. `None` when a part can't be
/// written, like `{$sqrt(i x)$}`.
pub(super) fn split(f: &Complex) -> Option<(Expr, Expr)> {
    split_with(f, Split::default())
}

/// How [`split_with`] splits a term.
#[derive(Clone, Copy, Default)]
pub(super) struct Split<'a> {
    /// The symbol `z` of `(z, (a, b))` being `{$a + i b$}`.
    pub var: Option<(Symbol, &'a (Expr, Expr))>,
    /// Whether parts which only have a numerical form may be written, for graphs: `{$zeta$}` and `{$Gamma$}` of
    /// non-real arguments as internal functions (see [`Context::complex_part`]), and the principal argument as
    /// `{$2 atan(v / (|z| + u))$}` when the signs of the parts are unknown.
    pub numeric: bool,
}

/// The parts `{$(u, v)$}` of `{$f = u + i v$}` like [`split`], with the options `split`.
pub(super) fn split_with(f: &Complex, split: Split) -> Option<(Expr, Expr)> {
    let var = split.var;
    Some(match f {
        Term::Value(z) => (value(z.value[0].clone()), value(z.value[1].clone())),
        Term::Symbol(s) => match var {
            Some((z, parts)) if s.symbol == z => parts.clone(),
            _ => (variable(s.symbol), zero()),
        },
        Term::Add(add) => add.iter().try_fold((zero(), zero()), |(u, v), term| {
            let (a, b) = split_with(term, split)?;
            Some((u + a, v + b))
        })?,
        Term::Mul(mul) => {
            let c = &mul.coefficient;
            mul.iter()
                .try_fold((value(c[0].clone()), value(c[1].clone())), |z, factor| {
                    Some(product(&z, &split_with(factor, split)?))
                })?
        }
        Term::Pow(pow) => split_pow(&pow.base, &pow.exponant, split)?,
        Term::Fun(function) => {
            let args = function.get_args::<C<R<Rational>>>()?;
            let parts = args
                .iter()
                .map(|arg| split_with(arg, split))
                .collect::<Option<Vec<_>>>()?;
            split_fun(function.get_ident(), &parts, split.numeric)?
        }
    })
}

/// Whether `f` has no symbols other than builtin constants, so that its parts are those of [`split`] (in plain
/// normalization, symbols aren't assumed real: `{$re(x)$}` stays unevaluated).
pub(super) fn is_constant(f: &Complex) -> bool {
    let mut indices = Vec::new();
    held_sum_indices(f, &mut indices);
    f.symbols()
        .into_iter()
        .all(|s| Context::is_builtin_constant(s) || indices.contains(&s))
}

/// Push the indices of the held sums of `f` (bound symbols, so they don't make `f` depend on them).
fn held_sum_indices(f: &Complex, indices: &mut Vec<Symbol>) {
    match f {
        Term::Value(_) | Term::Symbol(_) => {}
        Term::Add(add) => add.iter().for_each(|term| held_sum_indices(term, indices)),
        Term::Mul(mul) => mul.iter().for_each(|term| held_sum_indices(term, indices)),
        Term::Pow(pow) => {
            held_sum_indices(&pow.base, indices);
            held_sum_indices(&pow.exponant, indices);
        }
        Term::Fun(function) => {
            let Some(args) = function.get_args::<C<R<Rational>>>() else {
                return;
            };
            if function.get_ident() == Context::held_sum()
                && let Some(Term::Symbol(k)) = args.get(1)
            {
                indices.push(k.symbol);
            }
            for arg in args {
                held_sum_indices(arg, indices);
            }
        }
    }
}

/// `{$re z$}`, `{$im z$}`, `{$overline(z)$}` or `{$|z|$}` for a constant `z`, computed from its parts (`{$|z|$}` only when
/// `z` isn't real, since the real `abs` would come back here).
pub(super) fn constant_part(ident: Symbol, z: &Complex) -> Option<Complex> {
    if !is_constant(z) {
        return None;
    }
    let (u, v) = split(z)?;
    match ident {
        Context::RE => join(&u, &zero()),
        Context::IM => join(&v, &zero()),
        Context::CONJ => join(&u, &-v),
        Context::ABS if !v.is_zero() => join(&modulus(&u, &v), &zero()),
        _ => None,
    }
}

/// The principal logarithm `{$ln z = ln|z| + i arg z$}` of a constant `z` which isn't a positive real number.
pub(super) fn principal_ln(z: &Complex) -> Option<Complex> {
    if !is_constant(z) {
        return None;
    }
    let (u, v) = split(z)?;
    if !is_complex_ln(&u, &v) {
        return None;
    }
    let (a, b) = split_ln(&u, &v, false)?;
    join(&a, &b)
}

/// `{$"Ci"(z) = "Ci"(-z) + i pi$}` for a negative real constant `z`, the principal value.
pub(super) fn negative_ci(z: &Complex) -> Option<Complex> {
    if !is_constant(z) {
        return None;
    }
    let (u, v) = split(z)?;
    if !is_ci_of_negative(&u, &v) {
        return None;
    }
    join(&fun(Context::CI, -u), &variable(Context::PI))
}

fn is_ci_of_negative(u: &Expr, v: &Expr) -> bool {
    v.is_zero() && sign(u, SignMode::APPROXIMATE) == Some(Ordering::Less)
}

/// `{$u + i v$}` as a complex expression, simplified when it is small (simplifying sums of several
/// exponentials and trigonometric functions may not finish).
pub(super) fn join(u: &Expr, v: &Expr) -> Option<Complex> {
    /// Size of the parts above which they are only normalized.
    const MAX_SIMPLIFIED: usize = 40;
    let res = to_complex(u)? + Term::Value(Value::new(C.i(), C)) * to_complex(v)?;
    let res = if size(u) + size(v) <= MAX_SIMPLIFIED {
        res.simplify()
    } else {
        res.normalize()
    };
    // `{$c/d = 1/(d/c)$}` for a non-real constant `c`, so `{$-i/(2 pi t - i) = 1/(2 i pi t + 1)$}`
    if let Term::Mul(mul) = &res
        && mul.coefficient[1] != 0
        && let [Term::Pow(pow)] = mul.factors.as_slice()
        && let Term::Value(e) = &**pow.exponant
        && C.is_one(&C.neg(&e.value))
    {
        let c = Term::Value(Value::new(mul.coefficient.clone(), C));
        return Some((&*pow.base / &c).expand().inv());
    }
    Some(res)
}

/// Whether `f` is a constant radical expression: Gaussian rationals and roots of positive rationals or of positive
/// real radical sums, with sums, products and integer powers.
pub(super) fn is_radical_constant(f: &Complex) -> bool {
    if f.is_approximate() {
        return false;
    }
    match f {
        Term::Value(_) => true,
        Term::Add(add) => add.iter().all(is_radical_constant),
        Term::Mul(mul) => mul.iter().all(is_radical_constant),
        Term::Pow(pow) => match (&*pow.base, &**pow.exponant) {
            (Term::Value(b), Term::Value(e)) => {
                b.value[1] == 0 && b.value[0] > 0 && e.value[1] == 0
            }
            // Integer powers of sums, and nested roots of positive real sums
            (base @ Term::Add(_), Term::Value(e)) => {
                e.value[1] == 0
                    && is_radical_constant(base)
                    && (e.value[0].denominator_ref() == &1u32
                        || split(base).is_some_and(|(u, v)| {
                            v.is_zero() && expr::constant_sign(&u) == Some(Ordering::Greater)
                        }))
            }
            _ => false,
        },
        Term::Symbol(_) | Term::Fun(_) => false,
    }
}

/// Whether `f` contains a nested root, a non-integer power of a sum.
pub(super) fn has_nested_root(f: &Complex) -> bool {
    match f {
        Term::Value(_) | Term::Symbol(_) | Term::Fun(_) => false,
        Term::Add(add) => add.iter().any(has_nested_root),
        Term::Mul(mul) => mul.iter().any(has_nested_root),
        Term::Pow(pow) => {
            matches!((&*pow.base, &**pow.exponant), (Term::Add(_), Term::Value(e))
                if e.value[0].denominator_ref() != &1u32)
                || has_nested_root(&pow.base)
        }
    }
}

/// The product of the constant radical factors `factors` and of `c`, expanded through its parts, the real ones
/// rationalizing their denominators (`{$1/(sqrt(2) + i) = (sqrt(2) - i)/3$}`). `None` when a part can't be written.
pub(super) fn expand_radical_product(c: &[Rational; 2], factors: &[&Complex]) -> Option<Complex> {
    let (u, v) = factors
        .iter()
        .try_fold((value(c[0].clone()), value(c[1].clone())), |z, f| {
            Some(product(&z, &split(f)?))
        })?;
    join_expanded(&u, &v)
}

/// The constant radical sum `f` with its parts expanded, so that its nested roots have the canonical form of
/// [`R`]'s expansion. `None` when a part can't be written.
pub(super) fn expand_radical_sum(f: &Complex) -> Option<Complex> {
    let (u, v) = split(f)?;
    let i = Term::Value(Value::new(C.i(), C));
    Some(to_complex(&u.expand())? + i * to_complex(&v.expand())?)
}

/// `{$u + i v$}` with both parts expanded, and the positive content of their rational coefficients out, as real
/// radical sums are written: `{$(sqrt(2) - i)/3$}`.
fn join_expanded(u: &Expr, v: &Expr) -> Option<Complex> {
    let terms = |t: Expr| match t {
        Term::Add(add) => add.iter().cloned().collect(),
        t => vec![t],
    };
    let (u, v) = (terms(u.expand()), terms(v.expand()));
    let coefficient = |t: &Expr| match t {
        Term::Value(c) => c.value.clone(),
        Term::Mul(mul) => mul.coefficient.clone(),
        _ => Rational::ONE,
    };
    let content = radicals::content(u.iter().chain(&v).map(coefficient));
    if content == 0u32 {
        return Some(Term::zero(C));
    }
    let scale = value(Rational::ONE / &content);
    let i = Term::Value(Value::new(C.i(), C));
    let sum = u.iter().try_fold(Term::zero(C), |res, t| {
        Some(res + to_complex(&(t * &scale))?)
    })?;
    let sum = v
        .iter()
        .try_fold(sum, |res, t| Some(res + &i * &to_complex(&(t * &scale))?))?;
    Some(Term::Value(Value::new([content, Rational::ZERO], C)) * sum)
}

/// The real expression `f` as a complex expression, normalized. `None` for functions with non-real arguments.
pub(super) fn to_complex(f: &Expr) -> Option<Complex> {
    Some(match f {
        Term::Value(_) | Term::Symbol(_) => C.try_from_expr(f.clone()).ok()?,
        Term::Add(add) => add
            .iter()
            .try_fold(Term::zero(C), |res, term| Some(res + to_complex(term)?))?,
        Term::Mul(mul) => mul.iter().try_fold(
            Term::Value(Value::new([mul.coefficient.clone(), Rational::ZERO], C)),
            |res, factor| Some(res * to_complex(factor)?),
        )?,
        Term::Pow(pow) => to_complex(&pow.base)?.pow(&to_complex(&pow.exponant)?),
        Term::Fun(function) => {
            let args = function.get_args::<Real>()?;
            let args = args.iter().map(to_complex).collect::<Option<_>>()?;
            Term::Fun(Box::new(Fun::new(function.get_ident(), args, C))).normalize()
        }
    })
}

/// `f` as a real expression with the imaginary unit replaced by the symbol `t`. With `analytic`, only when `f` is
/// built from rational functions and entire functions (`exp`, `sin`, `cos`, `sinh`, `cosh`, `erf`), so that an
/// identity between power series in `{$x$}` found for a real `t` stays true at `{$t = i$}`; otherwise any term, for
/// algebraic rules like derivatives, which commute with `{$t = i$}`. `None` when it can't be written.
pub(super) fn with_unit(f: &Complex, t: Symbol, analytic: bool) -> Option<Expr> {
    let gaussian = |z: &[Rational; 2]| value(z[0].clone()) + value(z[1].clone()) * variable(t);
    Some(match f {
        Term::Value(z) => gaussian(&z.value),
        Term::Symbol(s) => variable(s.symbol),
        Term::Add(add) => add.iter().try_fold(zero(), |res, term| {
            Some(res + with_unit(term, t, analytic)?)
        })?,
        Term::Mul(mul) => mul
            .iter()
            .try_fold(gaussian(&mul.coefficient), |res, factor| {
                Some(res * with_unit(factor, t, analytic)?)
            })?,
        Term::Pow(pow) => match &**pow.exponant {
            Term::Value(e) if e.value[1] == 0 && e.value[0].denominator_ref() == &1u32 => {
                with_unit(&pow.base, t, analytic)?.pow(&value(e.value[0].clone()))
            }
            _ if analytic => return None,
            exponant => with_unit(&pow.base, t, analytic)?.pow(&with_unit(exponant, t, analytic)?),
        },
        Term::Fun(function) => {
            let ident = function.get_ident();
            if analytic
                && ![
                    Context::EXP,
                    Context::SIN,
                    Context::COS,
                    Context::SINH,
                    Context::COSH,
                    Context::ERF,
                ]
                .contains(&ident)
            {
                return None;
            }
            let args = function
                .get_args::<C<R<Rational>>>()?
                .iter()
                .map(|arg| with_unit(arg, t, analytic))
                .collect::<Option<_>>()?;
            Term::Fun(Box::new(Fun::new(ident, args, R))).normalize()
        }
    })
}

/// The real expression `f` as a complex expression with the symbol `t` replaced by the imaginary unit, the inverse
/// of [`with_unit`]. `None` for functions with non-real arguments other than those of `t`.
pub(super) fn from_unit(f: &Expr, t: Symbol) -> Option<Complex> {
    Some(match f {
        Term::Symbol(s) if s.symbol == t => Term::Value(Value::new(C.i(), C)),
        Term::Value(_) | Term::Symbol(_) => C.try_from_expr(f.clone()).ok()?,
        Term::Add(add) => add
            .iter()
            .try_fold(Term::zero(C), |res, term| Some(res + from_unit(term, t)?))?,
        Term::Mul(mul) => mul.iter().try_fold(
            Term::Value(Value::new([mul.coefficient.clone(), Rational::ZERO], C)),
            |res, factor| Some(res * from_unit(factor, t)?),
        )?,
        Term::Pow(pow) => from_unit(&pow.base, t)?.pow(&from_unit(&pow.exponant, t)?),
        Term::Fun(function) => {
            let args = function.get_args::<Real>()?;
            let args = args
                .iter()
                .map(|arg| from_unit(arg, t))
                .collect::<Option<_>>()?;
            Term::Fun(Box::new(Fun::new(function.get_ident(), args, C))).normalize()
        }
    })
}

/// The real expression `f`, if its imaginary part is zero.
pub(super) fn real(f: &Complex) -> Option<Expr> {
    let (u, v) = split(f)?;
    v.is_zero().then_some(u)
}

/// `{$(a + i b)(c + i d)$}`.
fn product((a, b): &(Expr, Expr), (c, d): &(Expr, Expr)) -> (Expr, Expr) {
    if b.is_zero() && d.is_zero() {
        return (a * c, zero());
    }
    (a * c - b * d, a * d + b * c)
}

/// The parts of `{$z^n$}` for an integer `n`, by repeated squaring. `None` for a non-real `z` and `{$|n|$}` above
/// [`MAX_EXPONANT`].
fn integer_pow((u, v): (Expr, Expr), n: &Integer) -> Option<(Expr, Expr)> {
    if v.is_zero() {
        return Some((u.pow(&value(Rational::from(n))), zero()));
    }
    let mut k = u64::try_from(&n.unsigned_abs()).ok()?;
    if k > MAX_EXPONANT {
        return None;
    }
    // `{$z^(-k) = overline(z)^k / |z|^(2k)$}`
    let (base, scale) = if *n < 0 {
        let norm = &u * &u + &v * &v;
        ((u, -v), norm.pow(&value(Rational::from(n))))
    } else {
        ((u, v), one())
    };
    let (mut res, mut square) = ((one(), zero()), base);
    while k > 0 {
        if k & 1 == 1 {
            res = product(&res, &square);
        }
        square = product(&square, &square);
        k >>= 1;
    }
    Some((&res.0 * &scale, &res.1 * &scale))
}

/// The parts of `{$b^e$}`.
fn split_pow(base: &Complex, exponant: &Complex, split: Split) -> Option<(Expr, Expr)> {
    let (u, v) = split_with(base, split)?;
    if let Term::Value(e) = exponant
        && e.value[1] == 0
        && let Ok(n) = Integer::try_from(&e.value[0])
        && let Some(parts) = integer_pow((u.clone(), v.clone()), &n)
    {
        return Some(parts);
    }
    let e = split_with(exponant, split)?;
    if !is_complex_ln(&u, &v) {
        // `{$b^(a + i c) = e^((a + i c) ln b)$}` for `{$b > 0$}`
        let positive =
            u == variable(Context::E) || sign(&u, SignMode::APPROXIMATE) == Some(Ordering::Greater);
        if e.1.is_zero() {
            return Some((u.pow(&e.0), zero()));
        }
        if !positive {
            return None;
        }
        let ln = fun(Context::LN, u);
        return split_fun(Context::EXP, &[(&e.0 * &ln, &e.1 * &ln)], split.numeric);
    }
    // The principal power `{$z^w = e^(w ln z)$}`
    let ln = split_ln(&u, &v, split.numeric)?;
    split_fun(Context::EXP, &[product(&e, &ln)], split.numeric)
}

/// Whether `{$ln(u + i v)$}` isn't real: `v` is non-zero, or `u` is negative.
fn is_complex_ln(u: &Expr, v: &Expr) -> bool {
    !v.is_zero() || sign(u, SignMode::APPROXIMATE) == Some(Ordering::Less)
}

/// The parts of the principal logarithm `{$ln(u + i v) = ln|z| + i arg z$}`, `None` when the argument can't be
/// found. With `numeric`, an argument depending on unknown signs is `{$2 atan(v / (|z| + u))$}`, undefined on the
/// branch cut.
fn split_ln(u: &Expr, v: &Expr, numeric: bool) -> Option<(Expr, Expr)> {
    let arg = match expr::arg(u, v) {
        Some(arg) => arg,
        None if numeric => value(Rational::from(2)) * fun(Context::ATAN, v / &(modulus(u, v) + u)),
        None => return None,
    };
    if v.is_zero() {
        return Some((fun(Context::LN, -u), arg));
    }
    let norm = norm(u, v);
    // `{$ln|z|$}` when the root of the norm is simplified, like `{$ln|3 + 4 i| = ln 5$}`, else `{$ln(|z|^2)/2$}`
    let modulus = norm.pow(&half());
    let ln = if matches!(modulus, Term::Pow(_)) {
        fun(Context::LN, norm) * half()
    } else {
        fun(Context::LN, modulus)
    };
    Some((ln, arg))
}

/// `{$u^2 + v^2$}`, simplified when it is small, so that `{$cos^2 a + sin^2 a = 1$}` and `{$ln(e^i) = i$}`.
fn norm(u: &Expr, v: &Expr) -> Expr {
    /// Size above which it isn't simplified.
    const MAX_SIMPLIFIED: usize = 40;
    let norm = u * u + v * v;
    if size(&norm) <= MAX_SIMPLIFIED {
        fun(Context::SIMPLIFY, norm)
    } else {
        norm
    }
}

/// `{$|u + i v| = sqrt(u^2 + v^2)$}`.
fn modulus(u: &Expr, v: &Expr) -> Expr {
    norm(u, v).pow(&half())
}

/// The parts of `{$f(z_1, ..., z_n)$}`, with numerical forms when `numeric` (see [`Split::numeric`]).
fn split_fun(ident: Symbol, args: &[(Expr, Expr)], numeric: bool) -> Option<(Expr, Expr)> {
    match (ident, args) {
        (Context::RE, [(u, _)]) => Some((u.clone(), zero())),
        (Context::IM, [(_, v)]) => Some((v.clone(), zero())),
        (Context::CONJ, [(u, v)]) => Some((u.clone(), -v)),
        (Context::ABS, [(u, v)]) if !v.is_zero() => Some((modulus(u, v), zero())),
        (Context::LN, [(u, v)]) if is_complex_ln(u, v) => split_ln(u, v, numeric),
        (Context::CI, [(u, v)]) if is_ci_of_negative(u, v) => {
            Some((fun(Context::CI, -u), variable(Context::PI)))
        }
        _ if args.iter().all(|(_, v)| v.is_zero()) => {
            let args = args.iter().map(|(u, _)| u.clone()).collect();
            Some((
                Term::Fun(Box::new(Fun::new(ident, args, R))).normalize(),
                zero(),
            ))
        }
        // `{$e^(a + i b) = e^a (cos b + i sin b)$}`
        (Context::EXP, [(a, b)]) => {
            let exp = fun(Context::EXP, a.clone());
            Some((
                &exp * &fun(Context::COS, b.clone()),
                exp * fun(Context::SIN, b.clone()),
            ))
        }
        // `{$sin(a + i b) = sin a cosh b + i cos a sinh b$}`, `{$cos(a + i b) = cos a cosh b - i sin a sinh b$}`
        (Context::SIN | Context::COS, [(a, b)]) => {
            let (sin, cos) = (fun(Context::SIN, a.clone()), fun(Context::COS, a.clone()));
            let (sinh, cosh) = (fun(Context::SINH, b.clone()), fun(Context::COSH, b.clone()));
            Some(if ident == Context::SIN {
                (sin * cosh, cos * sinh)
            } else {
                (cos * cosh, -(sin * sinh))
            })
        }
        // Held sums are linear, so `{$sum (u_k + i v_k) = sum u_k + i sum v_k$}` when the sum converges
        (_, [(u, v), (k, _), bounds @ ..]) if ident == Context::held_sum() => {
            let held = |body: &Expr| {
                if body.is_zero() {
                    return zero();
                }
                let mut args = vec![body.clone(), k.clone()];
                args.extend(bounds.iter().map(|(a, _)| a.clone()));
                Term::Fun(Box::new(Fun::new(ident, args, R))).normalize()
            };
            Some((held(u), held(v)))
        }
        (Context::ZETA | Context::GAMMA, [(a, b)]) if numeric => Some(numeric_parts(ident, a, b)),
        // `{$z! = Gamma(z + 1)$}`
        (Context::FACTORIAL, [(a, b)]) if numeric => {
            Some(numeric_parts(Context::GAMMA, &(a + &one()), b))
        }
        _ => None,
    }
}

/// The parts of `{$f(a + i b)$}` as the internal functions of [`Context::complex_part`], which only have a
/// numerical form.
fn numeric_parts(ident: Symbol, a: &Expr, b: &Expr) -> (Expr, Expr) {
    let part = |imaginary| {
        let args = vec![a.clone(), b.clone()];
        Term::Fun(Box::new(Fun::new(
            Context::complex_part(ident, imaginary),
            args,
            R,
        )))
        .normalize()
    };
    (part(false), part(true))
}
