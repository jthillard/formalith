//! The complex field `{$CC$}`.

use std::cmp::Ordering;

use malachite::{
    Integer, Natural, Rational,
    base::num::{
        arithmetic::traits::{Abs, Lcm, Sign, UnsignedAbs},
        basic::traits::{One, Zero},
    },
};

use crate::{
    context::{Context, Symbol},
    field::{
        Derivable, Field, Group, PartiallyOrderedSet, Ring, Set, SetParseExpression,
        TryElementFrom, TryExprFrom, cartesian::CartesianPower, matrix::M, real::R,
    },
    parser::{Parser, lexer::TokenKind},
    printer::{PrettyPrinter, PrintOptions},
    term::{self, Expand, Fun, Mul, Normalize, Term, TermSet, Value},
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

    /// Compute `base^exponant` using exponentiation by squaring.
    ///
    /// Returns `None` for negative powers of zero or too large exponants.
    fn pow_integer(&self, base: &[Rational; 2], exponant: &Integer) -> Option<[Rational; 2]> {
        let base = if *exponant < 0 {
            self.try_inv(base)?
        } else {
            base.clone()
        };
        let mut remaining = u64::try_from(exponant.unsigned_abs_ref()).ok()?;
        let (mut res, mut square) = (self.one(), base);
        while remaining != 0 {
            if remaining & 1 == 1 {
                res = self.mul(&res, &square);
            }
            square = self.mul(&square, &square);
            remaining >>= 1;
        }
        Some(res)
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
            Term::Mul(mul) if ident == Context::CONJ => {
                Some(mul.iter().fold(Term::one(self), |res, factor| {
                    res * self.fun(ident, factor.clone())
                }))
            }
            _ => None,
        }
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
            let res = real.normalize(Term::Pow(term::Pow::new(
                Term::Value(Value::new(base.clone(), real)),
                Term::Value(Value::new(exponant.clone(), real)),
                real,
            )));
            return self.try_from_expr(res).ok();
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
        let [re, im] = elem;
        if *im == 0 {
            return self.real().print(re, options, f);
        }
        if *re != 0 {
            self.real().print(re, options, f)?;
            write!(f, "{}", if *im < 0 { "-" } else { "+" })?;
        } else if *im < 0 {
            write!(f, "-")?;
        }
        let magnitude = im.abs();
        if magnitude != 1 {
            self.real().print(&magnitude, options, f)?;
            write!(f, "{}", if options.typst { " " } else { "*" })?;
        }
        write!(f, "i")
    }
    fn pretty_print(&self, elem: &Self::Element, options: &PrintOptions) -> PrettyPrinter {
        let [re, im] = elem;
        if *im == 0 {
            return self.real().pretty_print(re, options);
        }
        let i = PrettyPrinter::from("i".to_string());
        let magnitude = im.abs();
        let imaginary = if magnitude == 1 {
            i
        } else {
            let mut res = self.real().pretty_print(&magnitude, options);
            res.concat("⋅", false, &i);
            res
        };
        if *re != 0 {
            let mut res = self.real().pretty_print(re, options);
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
}

impl Group for C<R<Rational>> {
    fn zero(&self) -> Self::Element {
        self.plane.zero()
    }

    fn nth(&self, nth: i64) -> Self::Element {
        [self.real().nth(nth), Rational::ZERO]
    }

    fn add(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        self.plane.add(a, b)
    }

    fn neg(&self, a: &Self::Element) -> Self::Element {
        self.plane.neg(a)
    }

    fn to_i64(&self, a: &Self::Element) -> Option<i64> {
        Self::as_integer(a).and_then(|n| i64::try_from(&n).ok())
    }
}

impl Ring for C<R<Rational>> {
    fn one(&self) -> Self::Element {
        [Rational::ONE, Rational::ZERO]
    }

    fn mul(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        let ([a, b], [c, d]) = (a, b);
        [a * c - b * d, a * d + b * c]
    }

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
                ident @ (Context::RE | Context::IM | Context::CONJ) => {
                    if let Some(res) = fun
                        .get_arg::<Self>()
                        .and_then(|arg| self.eval_part(ident, arg))
                    {
                        return res;
                    }
                }
                Context::EXPAND => {
                    if let Some(arg) = fun.get_arg::<Self>() {
                        return arg.expand();
                    }
                }
                Context::FACTOR => {
                    if let Some(arg) = fun.get_arg::<Self>() {
                        return arg.factor();
                    }
                }
                Context::SIMPLIFY => {
                    if let Some(arg) = fun.get_arg::<Self>() {
                        return arg.simplify();
                    }
                }
                Context::DIFF => {
                    if let Some([f, Term::Symbol(x)]) = fun.get_args::<Self>().map(Vec::as_slice) {
                        let res = f.derivative(x.symbol);
                        // `f` can't be differentiated, keep the term to avoid normalizing forever
                        if !matches!(&res, Term::Fun(inner)
                            if inner.get_ident() == Context::DIFF && inner.get_arg::<Self>() == Some(f))
                        {
                            return res;
                        }
                    }
                }
                Context::DET => {
                    if let Some(Term::Value(matrix)) = fun.get_arg::<M<TermSet<Self>>>()
                        && let Ok(res) = matrix.value.det()
                    {
                        return res;
                    }
                }
                _ => {}
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

/// The complex field, using [`malachite::rational::Rational`] for the real and imaginary parts to get arbitrary precision numbers.
pub const C: C<R<Rational>> = C::new(R);
