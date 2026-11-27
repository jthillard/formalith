//! The complex field `{$CC$}`.

mod approx;
mod parts;

use std::{cmp::Ordering, sync::LazyLock};

use malachite::{
    Integer, Natural, Rational,
    base::num::{
        arithmetic::traits::{Abs, Lcm, Sign},
        basic::traits::{One, Zero},
    },
};

use crate::term::fun::{eval_calculus_builtin, eval_ring_builtin};
use crate::{
    context::{Context, Symbol},
    field::{
        Derivable, Field, Group, Monoid, PartiallyOrderedSet, Ring, Semiring, Set,
        SetParseExpression, TryElementFrom, TryExprFrom,
        cartesian::CartesianPower,
        matrix::M,
        real::{
            R,
            approx::format_decimal,
            expr::{self, Expr, variable},
        },
    },
    integrate::{IntegrateError, apart_arguments},
    limit::{Direction, LimitError, remainder},
    parser::{Parser, lexer::TokenKind},
    printer::{PrettyPrinter, PrintOptions},
    term::{self, Fun, Mul, Normalize, SymbolTerm, Term, TermSet, Value},
};

/// The complex field `{$CC$}`, defined as the plane `{$RR^2$}` with the complex multiplication.
///
/// An element `[re, im]` represents the complex number `{$"re" + "im" i$}`. The imaginary unit is parsed from the identifier `i`.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(not(feature = "concise-debug"), derive(Debug))]
pub struct C<T> {
    pub(crate) plane: CartesianPower<T, 2>,
}

#[cfg(feature = "concise-debug")]
impl<T> std::fmt::Debug for C<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("C").finish()
    }
}

impl<T> C<T> {
    /// Create the complex field over the real field `real`.
    pub const fn new(real: T) -> Self {
        Self {
            plane: CartesianPower::new(real),
        }
    }
}

impl C<R<Rational>> {
    /// Get the real field this complex field is built on.
    const fn real(self) -> R<Rational> {
        self.plane.set
    }

    /// Get the imaginary unit `i`.
    #[must_use]
    pub const fn i(&self) -> [Rational; 2] {
        [Rational::ZERO, Rational::ONE]
    }

    /// Compute the complex conjugate of `a`.
    #[must_use]
    pub fn conj(&self, a: &[Rational; 2]) -> [Rational; 2] {
        [a[0].clone(), -&a[1]]
    }

    /// Return `a` as an integer, if it is one.
    fn as_integer(a: &[Rational; 2]) -> Option<Integer> {
        if a[1] == 0 {
            Integer::try_from(&a[0]).ok()
        } else {
            None
        }
    }

    /// Build the function `ident(arg)`, normalized.
    fn fun(self, ident: Symbol, arg: Term<Self>) -> Term<Self> {
        Term::Fun(Box::new(Fun::new(ident, vec![arg], self))).normalize()
    }

    /// Evaluate `re(arg)`, `im(arg)` or `conj(arg)`, using linearity on sums and products with a constant coefficient.
    fn eval_part(self, ident: Symbol, arg: &Term<Self>) -> Option<Term<Self>> {
        let value = |value| Term::Value(Value::new(value, self));
        match arg {
            Term::Value(Value { value: z, .. }) => Some(value(match ident {
                Context::RE => [z[0].clone(), Rational::ZERO],
                Context::IM => [z[1].clone(), Rational::ZERO],
                _ => self.conj(z),
            })),
            Term::Add(add) => Some(add.iter().fold(Term::zero(self), |res, term| {
                res + self.fun(ident, term.clone())
            })),
            Term::Mul(mul) if !self.is_one(&mul.coefficient) => {
                let c = &mul.coefficient;
                let rest = Term::Mul(Mul::new(self.one(), mul.factors.clone(), self)).normalize();
                let (re_c, im_c) = (
                    value([c[0].clone(), Rational::ZERO]),
                    value([c[1].clone(), Rational::ZERO]),
                );
                Some(match ident {
                    Context::RE => {
                        re_c * self.fun(Context::RE, rest.clone())
                            - im_c * self.fun(Context::IM, rest)
                    }
                    Context::IM => {
                        re_c * self.fun(Context::IM, rest.clone())
                            + im_c * self.fun(Context::RE, rest)
                    }
                    _ => value(self.conj(c)) * self.fun(Context::CONJ, rest),
                })
            }
            _ if parts::is_constant(arg) => parts::constant_part(ident, arg),
            // `{$overline(overline(z)) = z$}`
            Term::Fun(inner) if ident == Context::CONJ && inner.get_ident() == Context::CONJ => {
                inner.get_arg::<Self>().cloned()
            }
            Term::Mul(mul) if ident == Context::CONJ => {
                Some(mul.iter().fold(Term::one(self), |res, factor| {
                    res * self.fun(ident, factor.clone())
                }))
            }
            _ => None,
        }
    }

    /// The symbol `ident` as a term.
    const fn symbol(self, ident: Symbol) -> Term<Self> {
        Term::Symbol(SymbolTerm::new(ident, self))
    }

    /// The whole series of `f` in `{$x$}`, computed in `{$RR$}` with the imaginary unit as a real parameter `t` and
    /// `{$t = i$}` substituted back, so that `{$e^(i x)$}` has a single sum (see [`parts::with_unit`]).
    fn whole_series_with_unit(
        f: &Term<Self>,
        x: Symbol,
        point: &Expr,
        direction: &[Expr],
    ) -> Option<Term<Self>> {
        let t = *UNIT;
        let g = parts::with_unit(f, t, true)?;
        if !g.symbols().contains(&t) {
            return None;
        }
        let direction = Direction::from_args(direction)?;
        let res = g.infinite_series(x, point, direction).ok()?;
        parts::from_unit(&res, t)
    }

    /// Whether the calculus builtin `ident` of the parts `u + i v` of a function, with the other arguments
    /// `rest`, is the same in `{$RR$}` as with the principal branches of `{$CC$}`: the bases of powers and `ln`
    /// assumed real by the split (see [`parts::real_only_bases`]) must be positive near the point of `series`
    /// (their limit there), and of `lim` unless their limit is a negative constant (kept as it is, like
    /// `{$ln(-1) = i pi$}`, except by real roots of odd order), and non-negative between the bounds of a definite
    /// integral (by interval arithmetic). Antiderivatives found in `{$RR$}` are those of `{$CC$}`.
    fn principal_parts(ident: Symbol, u: &Expr, v: &Expr, x: Symbol, rest: &[Expr]) -> bool {
        let mut bases = vec![];
        parts::real_only_bases(u, x, &mut bases);
        parts::real_only_bases(v, x, &mut bases);
        if bases.is_empty() {
            return true;
        }
        match (ident, rest) {
            (Context::INTEGRATE, []) => true,
            (Context::INTEGRATE, [a, b]) => {
                // An interval containing both bounds
                let bound = |t: &Expr| crate::field::real::approx::enclose(t, 100);
                let (Some(a), Some(b)) = (bound(a), bound(b)) else {
                    return false;
                };
                let (lo, hi) = (a.lo().min(b.lo()), a.hi().max(b.hi()));
                bases.iter().all(|(base, _)| {
                    crate::limit::bounds::bounds_in(base, &[(x, (lo.clone(), hi.clone()))])
                        .is_some_and(|(l, _)| l >= 0)
                })
            }
            (Context::LIM | Context::SERIES, [point, ..]) => bases.iter().all(|(base, odd)| {
                base.limit(x, point, Direction::Both).is_ok_and(|l| {
                    l == variable(Context::OO)
                        || match expr::constant_sign(&l) {
                            Some(Ordering::Greater) => true,
                            Some(Ordering::Less) => ident == Context::LIM && !odd,
                            _ => false,
                        }
                })
            }),
            _ => false,
        }
    }

    /// Evaluate `integrate`, `lim` or `series` in `{$RR$}` on the real and imaginary parts of the function,
    /// every symbol being assumed real. The other arguments (bounds, point, order) must be real.
    fn eval_calculus(self, ident: Symbol, args: &[Term<Self>]) -> Option<Term<Self>> {
        let [f, Term::Symbol(x), rest @ ..] = args else {
            return None;
        };
        let x = x.symbol;
        let rest = rest.iter().map(parts::real).collect::<Option<Vec<_>>>()?;
        if ident == Context::SERIES
            && let [point, Term::Symbol(oo), direction @ ..] = rest.as_slice()
            && oo.symbol == Context::OO
            && let Some(res) = Self::whole_series_with_unit(f, x, point, direction)
        {
            return Some(res);
        }
        let (u, v) = parts::split(f)?;
        if !Self::principal_parts(ident, &u, &v, x, &rest) {
            return None;
        }
        // Each part is `Ok(Some(res))`, `Ok(None)` if unevaluated, or `Err(())` if it doesn't exist
        let eval = |part: &Expr| -> Result<Option<Expr>, ()> {
            match ident {
                Context::INTEGRATE => {
                    let res = match rest.as_slice() {
                        [] => part.integrate(x),
                        [a, b] => part.integrate_definite(x, a, b),
                        _ => return Ok(None),
                    };
                    match res {
                        Ok(res) => Ok(Some(res)),
                        Err(IntegrateError::Divergent(sign)) if v.is_zero() => {
                            let oo = variable(Context::OO);
                            Ok(Some(if sign == Ordering::Less { -oo } else { oo }))
                        }
                        Err(IntegrateError::Divergent(_) | IntegrateError::Undefined) => Err(()),
                        Err(IntegrateError::Unsupported | IntegrateError::NonElementary) => {
                            Ok(None)
                        }
                    }
                }
                Context::LIM => {
                    let [point, direction @ ..] = rest.as_slice() else {
                        return Ok(None);
                    };
                    let Some(direction) = Direction::from_args(direction) else {
                        return Ok(None);
                    };
                    match part.limit(x, point, direction) {
                        // An infinite part only makes sense for real limits
                        Ok(res) if v.is_zero() || !res.symbols().contains(&Context::OO) => {
                            Ok(Some(res))
                        }
                        Err(LimitError::Undefined) => Err(()),
                        _ => Ok(None),
                    }
                }
                _ => {
                    // The whole series of each part
                    if let [point, Term::Symbol(oo), direction @ ..] = rest.as_slice()
                        && oo.symbol == Context::OO
                    {
                        let Some(direction) = Direction::from_args(direction) else {
                            return Ok(None);
                        };
                        return Ok(part.infinite_series(x, point, direction).ok());
                    }
                    let (point, order, direction) = match rest.as_slice() {
                        [point] => (point, Rational::from(6), Some(Direction::Both)),
                        [point, Term::Value(order), direction @ ..] => {
                            (point, order.value.clone(), Direction::from_args(direction))
                        }
                        _ => return Ok(None),
                    };
                    let Some(direction) = direction else {
                        return Ok(None);
                    };
                    Ok(part.series(x, point, &order, direction).ok())
                }
            }
        };
        let res = (|| {
            let mut re = eval(&u)?;
            if ident == Context::SERIES
                && let Some(re) = &mut re
                && let [point, rest @ ..] = rest.as_slice()
                && !matches!(rest, [Term::Symbol(oo), ..] if oo.symbol == Context::OO)
            {
                let order = match rest {
                    [Term::Value(order), ..] => order.value.clone(),
                    _ => Rational::from(6),
                };
                *re = &*re + &remainder(x, point, &order);
            }
            let im = if v.is_zero() {
                Some(v.clone())
            } else {
                eval(&v)?
            };
            Ok(re.zip(im))
        })();
        match res {
            Ok(Some((re, im))) => parts::join(&re, &im),
            Ok(None) => None,
            Err(()) => Some(self.symbol(Context::UNDEFINED)),
        }
    }

    /// Print `{$"re" + "im" i$}`, the parts being printed by `part`.
    fn print_parts(
        elem: &[Rational; 2],
        options: PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
        part: impl Fn(&Rational, &mut std::fmt::Formatter<'_>) -> std::fmt::Result,
    ) -> std::fmt::Result {
        let [re, im] = elem;
        if *im == 0 {
            return part(re, f);
        }
        if *re != 0 {
            part(re, f)?;
            write!(f, "{}", if *im < 0 { "-" } else { "+" })?;
        } else if *im < 0 {
            write!(f, "-")?;
        }
        let magnitude = im.abs();
        if magnitude != 1 {
            part(&magnitude, f)?;
            write!(f, "{}", if options.typst { " " } else { "*" })?;
        }
        write!(f, "i")
    }

    /// Pretty print `{$"re" + "im" i$}`, the parts being printed by `part`.
    fn pretty_print_parts(
        elem: &[Rational; 2],
        part: impl Fn(&Rational) -> PrettyPrinter,
    ) -> PrettyPrinter {
        let [re, im] = elem;
        if *im == 0 {
            return part(re);
        }
        let i = PrettyPrinter::from("i".to_string());
        let magnitude = im.abs();
        let imaginary = if magnitude == 1 {
            i
        } else {
            let mut res = part(&magnitude);
            res.concat("⋅", false, &i);
            res
        };
        if *re != 0 {
            let mut res = part(re);
            res.concat(if *im < 0 { "-" } else { "+" }, true, &imaginary);
            res
        } else if *im < 0 {
            let mut res = PrettyPrinter::from("-".to_string());
            res.concat("", false, &imaginary);
            res
        } else {
            imaginary
        }
    }

    /// Evaluate `{$e^(q i pi)$}` for a half-integer `q`, which is 1, `i`, -1 or `-i`.
    fn eval_exp(self, arg: &Term<Self>) -> Option<Term<Self>> {
        let Term::Mul(mul) = arg else { return None };
        if !matches!(mul.iter().collect::<Vec<_>>().as_slice(),
            [Term::Symbol(symbol)] if symbol.symbol == Context::PI)
            || mul.coefficient[0] != 0
        {
            return None;
        }
        let half_turns = &mul.coefficient[1] * Rational::from(2);
        let quarters = i64::try_from(&half_turns).ok()?.rem_euclid(4);
        let z = match quarters {
            0 => [Rational::ONE, Rational::ZERO],
            1 => [Rational::ZERO, Rational::ONE],
            2 => [-Rational::ONE, Rational::ZERO],
            _ => [Rational::ZERO, -Rational::ONE],
        };
        Some(Term::Value(Value::new(z, self)))
    }

    /// The expansion of the constant radical factors of a product, with its coefficient, when one of them is a sum
    /// and there is another one or the coefficient isn't real (`{$sqrt(2) (1 + i sqrt(2)) = sqrt(2) + 2 i$}`). Other
    /// factors are kept.
    fn expand_radical_product(mul: &Mul<Self>) -> Option<Term<Self>> {
        let (radicals, rest): (Vec<&Term<Self>>, Vec<&Term<Self>>) =
            mul.iter().partition(|f| parts::is_radical_constant(f));
        if !radicals.iter().any(|f| matches!(f, Term::Add(_)))
            || (radicals.len() < 2 && mul.coefficient[1] == 0)
        {
            return None;
        }
        let product = parts::expand_radical_product(&mul.coefficient, &radicals)?;
        Some(rest.into_iter().fold(product, |res, f| res * f))
    }

    /// The principal value `{$z^w = e^(w ln z)$}` of a power with a non-real exponent, when it is real: `{$i^i =
    /// e^(-pi/2)$}`. Other powers, like `{$2^i$}`, are kept.
    fn principal_pow(self, base: &[Rational; 2], exponant: &[Rational; 2]) -> Option<Term<Self>> {
        let z = Term::Value(Value::new(base.clone(), self));
        if z.is_zero() {
            return None;
        }
        let ln = parts::principal_ln(&z).or_else(|| {
            // A positive real base, whose logarithm is real
            (base[1] == 0 && base[0] > 0).then(|| self.fun(Context::LN, z))
        })?;
        let (u, v) = parts::split(&(Term::Value(Value::new(exponant.clone(), self)) * ln))?;
        if !v.is_zero() {
            return None;
        }
        parts::to_complex(&expr::fun(Context::EXP, u))
    }

    /// Normalize `base^exponant` where both are constants.
    fn normalize_constant_pow(
        self,
        base: &[Rational; 2],
        exponant: &[Rational; 2],
    ) -> Option<Term<Self>> {
        if let Some(exponant) = Self::as_integer(exponant) {
            return self
                .pow_integer(base, &exponant)
                .map(|res| Term::Value(Value::new(res, self)));
        }
        if exponant[1] != 0 {
            return self.principal_pow(base, exponant);
        }
        if base[1] != 0 {
            return None;
        }
        let (base, exponant) = (&base[0], &exponant[0]);
        if *base >= 0 {
            // Real power of a positive real number, computed in the real field
            let real = self.real();
            let pow = Term::Pow(term::Pow::new(
                Term::Value(Value::new(base.clone(), real)),
                Term::Value(Value::new(exponant.clone(), real)),
                real,
            ));
            let res = real.normalize(pow.clone());
            if res == pow {
                return None;
            }
            // The conversion doesn't keep normalization flags, `{$(3/2)^(1/2) = 6^(1/2)/2$}`
            return self.try_from_expr(res).ok().map(|res| res.normalize());
        }
        if *exponant.denominator_ref() == 2 {
            // `{$(-a)^(p/2) = i^p a^(p/2)$}`
            let p = Integer::from_sign_and_abs(
                exponant.sign() == Ordering::Greater,
                exponant.numerator_ref().clone(),
            );
            let i_p = self.pow_integer(&self.i(), &p)?;
            let root = Term::Pow(term::Pow::new(
                Term::Value(Value::new([-base, Rational::ZERO], self)),
                Term::Value(Value::new([exponant.clone(), Rational::ZERO], self)),
                self,
            ))
            .normalize();
            return Some(Term::Value(Value::new(i_p, self)) * root);
        }
        None
    }
}

impl Set for C<R<Rational>> {
    type Element = [Rational; 2];
    type ExponantSet = Self;
    type ProductCoefficientSet = Self;

    fn get_exponant_set(&self) -> Self::ExponantSet {
        *self
    }
    fn get_coefficient_set(&self) -> Self::ProductCoefficientSet {
        *self
    }
    fn print(
        &self,
        elem: &Self::Element,
        options: &PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        Self::print_parts(elem, *options, f, |x, f| self.real().print(x, options, f))
    }
    fn pretty_print(&self, elem: &Self::Element, options: &PrintOptions) -> PrettyPrinter {
        Self::pretty_print_parts(elem, |x| self.real().pretty_print(x, options))
    }
    fn print_approximate(
        &self,
        elem: &Self::Element,
        options: &PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        Self::print_parts(elem, *options, f, |x, f| {
            f.write_str(&format_decimal(x, options.typst))
        })
    }
    fn pretty_print_approximate(
        &self,
        elem: &Self::Element,
        _options: &PrintOptions,
    ) -> PrettyPrinter {
        Self::pretty_print_parts(elem, |x| PrettyPrinter::from(format_decimal(x, false)))
    }
    fn element_eq(&self, a: &Self::Element, b: &Self::Element) -> bool {
        self.plane.element_eq(a, b)
    }
    fn is_atomic(&self, elem: &Self::Element) -> bool {
        elem[1] == 0 || (elem[0] == 0 && elem[1] == 1)
    }
    fn is_sum(&self, elem: &Self::Element) -> bool {
        elem[0] != 0 && elem[1] != 0
    }
}

impl PartiallyOrderedSet for C<R<Rational>> {
    /// Complex numbers are only compared when they are real numbers.
    fn partial_cmp(&self, a: &Self::Element, b: &Self::Element) -> Option<Ordering> {
        if a == b {
            Some(Ordering::Equal)
        } else if a[1] == 0 && b[1] == 0 {
            self.real().partial_cmp(&a[0], &b[0])
        } else {
            None
        }
    }
    /// Lexicographic order, real part first.
    fn total_cmp(&self, a: &Self::Element, b: &Self::Element) -> Ordering {
        self.plane.total_cmp(a, b)
    }
}

impl Monoid for C<R<Rational>> {
    fn zero(&self) -> Self::Element {
        self.plane.zero()
    }

    fn add(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        self.plane.add(a, b)
    }

    fn to_i64(&self, a: &Self::Element) -> Option<i64> {
        Self::as_integer(a).and_then(|n| i64::try_from(&n).ok())
    }
}

impl Group for C<R<Rational>> {
    fn nth(&self, nth: i64) -> Self::Element {
        [self.real().nth(nth), Rational::ZERO]
    }

    fn neg(&self, a: &Self::Element) -> Self::Element {
        self.plane.neg(a)
    }
}

impl Semiring for C<R<Rational>> {
    fn one(&self) -> Self::Element {
        [Rational::ONE, Rational::ZERO]
    }

    fn mul(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        let ([a, b], [c, d]) = (a, b);
        [a * c - b * d, a * d + b * c]
    }

    fn normalize(&self, a: Term<Self>) -> Term<Self> {
        match &a {
            Term::Pow(term::Pow { base, exponant, .. }) => match (&**base, &***exponant) {
                (Term::Value(base), Term::Value(exponant)) => {
                    if let Some(res) = self.normalize_constant_pow(&base.value, &exponant.value) {
                        return res;
                    }
                }
                (Term::Add(_), Term::Value(exponant))
                    if Self::as_integer(&exponant.value).is_some_and(|n| !(0..2).contains(&n))
                        && parts::is_radical_constant(&a)
                        && let Some(res) = parts::expand_radical_product(&self.one(), &[&a]) =>
                {
                    // `{$1/(1 + i sqrt(2)) = (1 - i sqrt(2))/3$}`, `{$(1 + i sqrt(3))^2 = 2 i sqrt(3) - 2$}`
                    return res;
                }
                (Term::Mul(mul), Term::Value(exponant))
                    if Self::as_integer(&exponant.value).is_some() =>
                {
                    // `{$(x y)^n = x^n y^n$}` only holds for integer `n`
                    return Term::distribute_pow(mul, &Term::Value(exponant.clone()));
                }
                (Term::Pow(base), Term::Value(exponant))
                    if Self::as_integer(&exponant.value).is_some() =>
                {
                    // `{$(z^a)^n = z^(a n)$}` only holds for integer `n`
                    return base
                        .base
                        .pow(&(&**base.exponant * &Term::Value(exponant.clone())));
                }
                _ => {}
            },
            // Poles at real constants, like `{$ln 0$}` and `{$tan(pi/2)$}`, are those of `{$RR$}`
            Term::Fun(fun)
                if matches!(
                    fun.get_ident(),
                    Context::LN
                        | Context::TAN
                        | Context::FACTORIAL
                        | Context::GAMMA
                        | Context::POLYGAMMA
                        | Context::ZETA
                        | Context::ATANH
                ) && fun
                    .get_args::<Self>()
                    .is_some_and(|args| args.iter().all(parts::is_constant))
                    && to_real(&a).is_some_and(|real| real.normalize().is_undefined()) =>
            {
                return Term::Symbol(SymbolTerm::new(Context::UNDEFINED, *self));
            }
            Term::Fun(fun) => match fun.get_ident() {
                Context::ABS => {
                    if let Some(Term::Value(z)) = fun.get_arg::<Self>() {
                        let [re, im] = &z.value;
                        let norm = [re * re + im * im, Rational::ZERO];
                        let half = [Rational::from_signeds(1, 2), Rational::ZERO];
                        return Term::Value(Value::new(norm, *self))
                            .pow(&Term::Value(Value::new(half, *self)));
                    }
                    if let Some(res) = fun
                        .get_arg::<Self>()
                        .and_then(|arg| parts::constant_part(Context::ABS, arg))
                    {
                        return res;
                    }
                    // `{$|z w| = |z| |w|$}`, so `{$|i x| = |x|$}`
                    if let Some(Term::Mul(mul)) = fun.get_arg::<Self>()
                        && (mul.factors.len() > 1 || !self.is_one(&mul.coefficient))
                    {
                        let coefficient = Term::Value(Value::new(mul.coefficient.clone(), *self));
                        return mul
                            .iter()
                            .fold(self.fun(Context::ABS, coefficient), |res, factor| {
                                res * self.fun(Context::ABS, factor.clone())
                            });
                    }
                }
                Context::LN => {
                    if let Some(res) = fun.get_arg::<Self>().and_then(parts::principal_ln) {
                        return res;
                    }
                }
                Context::CI => {
                    if let Some(res) = fun.get_arg::<Self>().and_then(parts::negative_ci) {
                        return res;
                    }
                }
                Context::APPROX => {
                    if let Some(res) = fun
                        .get_args::<Self>()
                        .and_then(|args| crate::field::real::approx::eval_approx(args))
                    {
                        return res;
                    }
                }
                Context::SQRT => {
                    if let Some(arg) = fun.get_arg::<Self>() {
                        let half = [Rational::from_signeds(1, 2), Rational::ZERO];
                        return arg.pow(&Term::Value(Value::new(half, *self)));
                    }
                }
                Context::ROOT => {
                    if let Some([arg, n]) = fun.get_args::<Self>().map(Vec::as_slice) {
                        return arg.pow(&n.inv());
                    }
                }
                Context::ARG => {
                    if let Some(res) = fun
                        .get_arg::<Self>()
                        .and_then(parts::split)
                        .and_then(|(u, v)| expr::arg(&u, &v))
                        .and_then(|res| parts::join(&res, &expr::zero()))
                    {
                        return res;
                    }
                }
                ident @ (Context::RE | Context::IM | Context::CONJ) => {
                    if let Some(res) = fun
                        .get_arg::<Self>()
                        .and_then(|arg| self.eval_part(ident, arg))
                    {
                        return res;
                    }
                }
                Context::EXP => {
                    if let Some(res) = fun.get_arg::<Self>().and_then(|arg| self.eval_exp(arg)) {
                        return res;
                    }
                }
                Context::FACTOR => {
                    if let Some(arg) = fun.get_arg::<Self>() {
                        return arg.factor();
                    }
                }
                Context::APART => {
                    if let Some(res) = fun
                        .get_args::<Self>()
                        .and_then(|args| apart_arguments(args))
                        .and_then(|(f, x)| f.apart(x))
                    {
                        return res;
                    }
                }
                Context::DIFF => {
                    if let Some(res) = eval_calculus_builtin(&**fun) {
                        return res;
                    }
                }
                Context::INTEGRATE | Context::LIM | Context::SERIES => {
                    if let Some(res) = fun
                        .get_args::<Self>()
                        .and_then(|args| self.eval_calculus(fun.get_ident(), args))
                    {
                        return res;
                    }
                }
                _ => {
                    if let Some(res) = eval_ring_builtin(&**fun) {
                        return res;
                    }
                }
            },
            Term::Mul(mul) => {
                if let Some(res) = Self::expand_radical_product(mul) {
                    return res;
                }
            }
            _ => {}
        }
        a
    }

    fn simplify(&self, a: Term<Self>) -> Term<Self> {
        a.cancel_common_factors()
    }

    fn expand(&self, a: Term<Self>) -> Term<Self> {
        if let Term::Pow(term::Pow { base, exponant, .. }) = &a
            && let Term::Add(add) = &**base
            && let Some(res) =
                Term::expand_integer_power(add, exponant, |c| [Rational::from(c), Rational::ZERO])
        {
            return res;
        }
        // Constant radical sums with nested roots are expanded through their parts, which have a canonical form
        if let Term::Add(_) = &a
            && parts::has_nested_root(&a)
            && parts::is_radical_constant(&a)
            && let Some(res) = parts::expand_radical_sum(&a)
        {
            return res;
        }
        a
    }
}

impl Ring for C<R<Rational>> {
    fn try_inv(&self, a: &Self::Element) -> Option<Self::Element> {
        if self.is_zero(a) {
            return None;
        }
        let norm = &a[0] * &a[0] + &a[1] * &a[1];
        Some([&a[0] / &norm, -&a[1] / norm])
    }

    fn as_fraction(&self, a: &Self::Element) -> (Self::Element, Self::Element) {
        let den = Rational::from(Natural::lcm(
            a[0].denominator_ref().clone(),
            a[1].denominator_ref().clone(),
        ));
        ([&a[0] * &den, &a[1] * &den], [den, Rational::ZERO])
    }

    fn coefficient_gcd(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        // The rational gcd of the components divides both numbers
        let gcd = [&a[1], &b[0], &b[1]]
            .into_iter()
            .fold(a[0].clone(), |gcd, x| R::gcd_rational(&gcd, x));
        [gcd, Rational::ZERO]
    }
}

impl Field for C<R<Rational>> {}

impl Derivable for C<R<Rational>> {
    fn derivative(&self, _: &Self::Element, _: Symbol) -> Self::Element {
        self.zero()
    }

    fn derivative_function(
        &self,
        fun: &dyn crate::term::Function<Self>,
        x: Symbol,
    ) -> Option<Term<Self>> {
        // A whole series, term by term, in `{$RR$}` with the imaginary unit as a parameter
        if fun.get_ident() != Context::held_sum() {
            return None;
        }
        let t = *UNIT;
        let sum = parts::with_unit(&Term::Fun(dyn_clone::clone_box(fun)), t, false)?;
        let Term::Fun(sum) = sum else {
            return None;
        };
        let res = crate::sum::derive_held_sum(sum.get_args::<R<Rational>>()?, x)?;
        parts::from_unit(&res, t)
    }
}

/// The imaginary unit as a real parameter, for the rules computed in `{$RR$}` (see [`parts::with_unit`]).
static UNIT: LazyLock<Symbol> = LazyLock::new(|| Symbol::new("@iunit"));

impl SetParseExpression for C<R<Rational>> {
    type MatrixArgumentSet = M<TermSet<Self>>;

    fn get_matrix_argument_set(&self) -> Self::MatrixArgumentSet {
        self.get_term_set().get_matrix_set()
    }

    fn parse_literal(&self, parser: &mut Parser) -> Result<Option<Self::Element>, String> {
        if matches!(&parser.token.kind, TokenKind::Ident(ident) if ident == "i") {
            parser.next_token();
            return Ok(Some(self.i()));
        }
        Ok(self
            .real()
            .parse_literal(parser)?
            .map(|re| [re, Rational::ZERO]))
    }

    fn is_constant(&self, name: &str) -> bool {
        name == "i"
    }
}

impl TryElementFrom<R<Rational>> for C<R<Rational>> {
    fn try_from_element(value: Rational) -> Result<Self::Element, super::TryCastError> {
        Ok([value, Rational::ZERO])
    }
}

impl TryElementFrom<C<Self>> for R<Rational> {
    fn try_from_element(value: [Rational; 2]) -> Result<Self::Element, super::TryCastError> {
        let [re, im] = value;
        if im == 0 {
            Ok(re)
        } else {
            Err(super::TryCastError("Can't cast a non real complex number"))
        }
    }
}

/// The type of [`C`], the complex numbers with rational parts.
pub type Complex = C<R<Rational>>;

/// The complex field, using [`malachite::rational::Rational`] for the real and imaginary parts to get arbitrary precision numbers.
pub const C: C<R<Rational>> = C::new(R);

/// The real and imaginary parts `{$(u, v)$}` of `{$f(a + i b) = u + i v$}`, for graphs.
///
/// They are functions of the real symbols `a` and `b`, the other symbols of `f` being assumed real. Parts may only have a numerical form: `{$zeta$}`
/// and `{$Gamma$}` of non-real arguments are internal functions evaluated by
/// [`Numeric`](crate::field::real::numeric::Numeric), and the principal argument of `{$ln$}` and powers is
/// `{$2 atan(v / (|z| + u))$}` when the signs of the parts are unknown. `None` when a part can't be written.
///
/// ```
/// use formalith::{field::{complex::{C, parts}, real::R}, parse, symbol};
///
/// let (u, v) = parts(&parse!("z^2", C), symbol!("z"), symbol!("x"), symbol!("y")).unwrap();
/// assert_eq!(u, parse!("x^2 - y^2", R));
/// assert_eq!(v, parse!("2*x*y", R));
/// ```
#[must_use]
pub fn parts(f: &Term<Complex>, z: Symbol, a: Symbol, b: Symbol) -> Option<(Expr, Expr)> {
    let var = (variable(a), variable(b));
    parts::split_with(
        f,
        parts::Split {
            var: Some((z, &var)),
            numeric: true,
        },
    )
}

/// The exact real and imaginary parts `{$(u, v)$}` of `{$f = u + i v$}`, every symbol of `f` being assumed real.
/// `None` when a part can't be written.
pub(crate) fn exact_parts(f: &Term<Complex>) -> Option<(Expr, Expr)> {
    parts::split(f)
}

/// The real expression `f` as a complex one, with its functions (which `TryExprFrom` doesn't convert). `None` for
/// functions with arguments in another set.
pub(crate) fn from_real(f: &Expr) -> Option<Term<Complex>> {
    parts::to_complex(f)
}

/// The real expression equal to the complex expression `f`, if it is real, every symbol being assumed real.
pub(crate) fn to_real(f: &Term<Complex>) -> Option<Expr> {
    TryExprFrom::<Complex>::try_from_expr(&R, f.clone())
        .ok()
        .or_else(|| parts::real(f))
}

/// The real and imaginary parts `{$(u, v)$}` of `{$f = u + i v$}`, every symbol of `f` being assumed real, for
/// graphs: parts may only have a numerical form, like in [`parts`]. `None` when a part can't be written.
///
/// ```
/// use formalith::{field::{complex::{C, real_parts}, real::R}, parse};
///
/// let (u, v) = real_parts(&parse!("exp(i*x)", C)).unwrap();
/// assert_eq!(u, parse!("cos(x)", R));
/// assert_eq!(v, parse!("sin(x)", R));
/// ```
#[must_use]
pub fn real_parts(f: &Term<Complex>) -> Option<(Expr, Expr)> {
    parts::split_with(
        f,
        parts::Split {
            var: None,
            numeric: true,
        },
    )
}
