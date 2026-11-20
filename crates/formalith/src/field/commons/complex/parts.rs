//! Real and imaginary parts of complex expressions, so that integrals, limits and series are computed in `{$RR$}`.

use std::cmp::Ordering;

use malachite::{
    Integer, Rational,
    base::num::{arithmetic::traits::UnsignedAbs, basic::traits::Zero},
};

use super::C;
use crate::{
    context::{Context, Symbol},
    field::{
        Group, Ring, TryExprFrom,
        real::{
            R,
            expr::{Expr, Real, fun, one, value, variable, zero},
            sign::{SignMode, sign},
        },
    },
    term::{Expand, Fun, Normalize, Term, Value},
};

/// A complex expression over `{$CC$}`.
type Complex = Term<C<R<Rational>>>;

/// The largest absolute integer exponent expanded by [`split`].
const MAX_EXPONANT: u64 = 16;

/// The parts `{$(u, v)$}` of `{$f = u + i v$}`, assuming every symbol is real. `None` when a part can't be
/// written, like `{$ln(i x)$}`.
pub(super) fn split(f: &Complex) -> Option<(Expr, Expr)> {
    Some(match f {
        Term::Value(z) => (value(z.value[0].clone()), value(z.value[1].clone())),
        Term::Symbol(s) => (variable(s.symbol), zero()),
        Term::Add(add) => add.iter().try_fold((zero(), zero()), |(u, v), term| {
            let (a, b) = split(term)?;
            Some((u + a, v + b))
        })?,
        Term::Mul(mul) => {
            let c = &mul.coefficient;
            mul.iter()
                .try_fold((value(c[0].clone()), value(c[1].clone())), |z, factor| {
                    Some(product(&z, &split(factor)?))
                })?
        }
        Term::Pow(pow) => split_pow(&pow.base, &pow.exponant)?,
        Term::Fun(function) => {
            let args = function.get_args::<C<R<Rational>>>()?;
            let parts = args.iter().map(split).collect::<Option<Vec<_>>>()?;
            split_fun(function.get_ident(), &parts)?
        }
    })
}

/// `{$u + i v$}` as a complex expression, simplified.
pub(super) fn join(u: &Expr, v: &Expr) -> Option<Complex> {
    let res = (to_complex(u)? + Term::Value(Value::new(C.i(), C)) * to_complex(v)?).simplify();
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

/// The real expression `f` as a complex expression, normalized. `None` for functions with non-real arguments.
fn to_complex(f: &Expr) -> Option<Complex> {
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

/// The parts of `{$z^n$}` for an integer `n`, by repeated squaring.
fn integer_pow((u, v): (Expr, Expr), n: &Integer) -> Option<(Expr, Expr)> {
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
fn split_pow(base: &Complex, exponant: &Complex) -> Option<(Expr, Expr)> {
    let (u, v) = split(base)?;
    if let Term::Value(e) = exponant
        && e.value[1] == 0
        && let Ok(n) = Integer::try_from(&e.value[0])
    {
        return integer_pow((u, v), &n);
    }
    if !v.is_zero() {
        return None;
    }
    let e = split(exponant)?;
    // `{$b^(a + i c) = e^((a + i c) ln b)$}` for `{$b > 0$}`
    let positive =
        u == variable(Context::E) || sign(&u, SignMode::APPROXIMATE) == Some(Ordering::Greater);
    if e.1.is_zero() {
        // Real powers of negative constants aren't real
        return (positive || !matches!(u, Term::Value(_))).then(|| (u.pow(&e.0), zero()));
    }
    if !positive {
        return None;
    }
    let ln = fun(Context::LN, u);
    split_fun(Context::EXP, &[(&e.0 * &ln, &e.1 * &ln)])
}

/// The parts of `{$f(z_1, ..., z_n)$}`.
fn split_fun(ident: Symbol, args: &[(Expr, Expr)]) -> Option<(Expr, Expr)> {
    match (ident, args) {
        (Context::RE, [(u, _)]) => Some((u.clone(), zero())),
        (Context::IM, [(_, v)]) => Some((v.clone(), zero())),
        (Context::CONJ, [(u, v)]) => Some((u.clone(), -v)),
        (Context::ABS, [(u, v)]) if !v.is_zero() => Some((
            (u * u + v * v).pow(&value(Rational::from_signeds(1, 2))),
            zero(),
        )),
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
        _ => None,
    }
}
