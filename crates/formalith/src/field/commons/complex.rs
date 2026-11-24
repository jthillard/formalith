//! The complex field `{$CC$}`.

mod approx;
mod parts;

use std::cmp::Ordering;

use malachite::{
    Integer, Natural, Rational,
    base::num::{
        arithmetic::traits::{Abs, Lcm, Sign, UnsignedAbs},
        basic::traits::{One, Zero},
    },
};

use crate::term::fun::{
    eval_algebra_builtin, eval_calculus_builtin, eval_degree, eval_matrix_builtin,
    eval_rewrite_builtin,
};
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

    /// Evaluate `integrate`, `lim` or `series` in `{$RR$}` on the real and imaginary parts of the function,
    /// every symbol being assumed real. The other arguments (bounds, point, order) must be real.
    fn eval_calculus(self, ident: Symbol, args: &[Term<Self>]) -> Option<Term<Self>> {
        let [f, Term::Symbol(x), rest @ ..] = args else {
            return None;
        };
        let x = x.symbol;
        let rest = rest.iter().map(parts::real).collect::<Option<Vec<_>>>()?;
        let (u, v) = parts::split(f)?;
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
        self,
        elem: &[Rational; 2],
        options: &PrintOptions,
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
        if base[1] != 0 || exponant[1] != 0 {
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
        self.print_parts(elem, options, f, |x, f| self.real().print(x, options, f))
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
        self.print_parts(elem, options, f, |x, f| {
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
                }
                Context::LN => {
                    if let Some(res) = fun.get_arg::<Self>().and_then(parts::principal_ln) {
                        return res;
                    }
                }
                Context::APPROX => {
                    if let Some(res) = fun
                        .get_args::<Self>()
                        .and_then(|args| approx::eval_approx(args))
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
                Context::EXPAND | Context::SIMPLIFY => {
                    if let Some(res) = eval_rewrite_builtin(&**fun) {
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
                Context::DET | Context::TRACE | Context::RANK | Context::CHARPOLY => {
                    if let Some(res) = eval_matrix_builtin(&**fun) {
                        return res;
                    }
                }
                Context::DEGREE => {
                    if let Some(res) = eval_degree(&**fun) {
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
                    if let Some(res) = eval_algebra_builtin(&**fun) {
                        return res;
                    }
                }
            },
            _ => {}
        }
        a
    }

    fn simplify(&self, a: Term<Self>) -> Term<Self> {
        a.cancel_common_factors()
    }

    fn expand(&self, a: Term<Self>) -> Term<Self> {
        if let Term::Pow(term::Pow { base, exponant, .. }) = &a
            && let Term::Value(exponant) = &***exponant
            && let Some(n) = Self::as_integer(&exponant.value)
        {
            match &**base {
                Term::Add(add) if n != 1 && n != -1 => {
                    if let Ok(k) = usize::try_from(&(&n).unsigned_abs()) {
                        let terms =
                            Term::expand_sum_power(add, k, |c| [Rational::from(c), Rational::ZERO]);
                        return if n < 0 {
                            term::Pow::new(terms, Term::nth(-1, *self), *self).into()
                        } else {
                            terms
                        };
                    }
                }
                _ => {}
            }
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
}

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

impl TryElementFrom<C<R<Rational>>> for R<Rational> {
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

/// The real and imaginary parts `{$(u, v)$}` of `{$f(a + i b) = u + i v$}`, as functions of the real symbols `a`
/// and `b`, the other symbols of `f` being assumed real, for graphs. Parts may only have a numerical form: `{$zeta$}`
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
