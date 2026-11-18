//! The real field `{$RR$}`.

pub(crate) mod approx;

use std::{cmp::Ordering, marker::PhantomData};

use malachite::{
    Natural, Rational,
    base::num::{
        arithmetic::traits::{Abs, Ceiling, CheckedRoot, Floor, Gcd, Lcm, Parity, Pow, Sign},
        basic::traits::{NegativeOne, One, Zero},
        conversion::traits::FromSciString,
    },
};

use crate::{
    context::{Context, Symbol},
    field::{
        Derivable, Field, Group, PartiallyOrderedSet, Ring, Set, SetParseExpression, matrix::M,
    },
    limit::{Direction, LimitError},
    parser::Parser,
    polynom::ToTerm,
    printer::PrettyPrinter,
    term::{self, Expand, Fun, Normalize, SymbolTerm, Term, TermSet, Value, flags::Flags},
};

/// The real field `{$RR$}`.
#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(not(feature = "concise-debug"), derive(Debug))]
pub struct R<T> {
    phantom: PhantomData<T>,
}

#[cfg(feature = "concise-debug")]
impl<T> std::fmt::Debug for R<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("R").finish()
    }
}

impl<T: Clone> Copy for R<T> {}

impl Set for R<Rational> {
    type Element = Rational;
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
        options: &crate::printer::PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        let (num, den) = elem.numerator_and_denominator_ref();
        if options.typst && *den != 1 {
            let sign = if *elem < 0 { "-" } else { "" };
            write!(f, "{sign}frac({num}, {den})")
        } else {
            write!(f, "{elem}")
        }
    }
    fn pretty_print(
        &self,
        elem: &Self::Element,
        _options: &crate::printer::PrintOptions,
    ) -> crate::printer::PrettyPrinter {
        let (num, den) = elem.numerator_and_denominator_ref();
        let mut res = PrettyPrinter::from(format!("{num}"));
        if *den != 1 {
            res.vertical_concat("─", &PrettyPrinter::from(format!("{den}")));
        }
        // The minus sign is in front of the fraction bar
        if elem.sign() == Ordering::Less {
            let mut minus = PrettyPrinter::from("-".to_string());
            minus.concat("", false, &res);
            res = minus;
        }
        res
    }
    fn print_approximate(
        &self,
        elem: &Self::Element,
        options: &crate::printer::PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        f.write_str(&approx::format_decimal(elem, options.typst))
    }
    fn pretty_print_approximate(
        &self,
        elem: &Self::Element,
        _options: &crate::printer::PrintOptions,
    ) -> crate::printer::PrettyPrinter {
        PrettyPrinter::from(approx::format_decimal(elem, false))
    }
    fn element_eq(&self, a: &Self::Element, b: &Self::Element) -> bool {
        a == b
    }
}

impl PartiallyOrderedSet for R<Rational> {
    fn partial_cmp(&self, a: &Self::Element, b: &Self::Element) -> Option<Ordering> {
        a.partial_cmp(b)
    }
}

impl Group for R<Rational> {
    fn zero(&self) -> Self::Element {
        Rational::ZERO
    }

    fn nth(&self, nth: i64) -> <Self::ProductCoefficientSet as Set>::Element {
        Rational::const_from_signed(nth)
    }

    fn add(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        a + b
    }

    fn neg(&self, a: &Self::Element) -> Self::Element {
        -a
    }

    fn to_i64(&self, a: &Self::Element) -> Option<i64> {
        i64::try_from(a).ok()
    }
}

impl Ring for R<Rational> {
    fn one(&self) -> Self::Element {
        Rational::ONE
    }

    fn mul(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        a * b
    }

    fn try_inv(&self, a: &Self::Element) -> Option<Self::Element> {
        if *a == 0 { None } else { Some(a.pow(-1_i64)) }
    }

    fn as_fraction(&self, a: &Self::Element) -> (Self::Element, Self::Element) {
        let sign = a.sign();
        let (num, den) = a.to_numerator_and_denominator();
        let (mut num, den) = (num.into(), den.into());
        if sign == Ordering::Less {
            num *= -Rational::ONE;
        }
        (num, den)
    }

    fn coefficient_gcd(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        Self::gcd_rational(a, b)
    }

    fn normalize(&self, a: Term<Self>) -> Term<Self> {
        match &a {
            Term::Pow(term::Pow { base, exponant, .. }) => match (&**base, &***exponant) {
                (Term::Mul(mul), Term::Value(value)) if value.value.denominator_ref() == &1 => {
                    // `{$(x y)^n = x^n y^n$}` for integer `n`
                    return Term::distribute_pow(mul, exponant);
                }
                (Term::Fun(fun), Term::Value(value))
                    if fun.get_ident() == Context::ABS && Self::is_even_integer(&value.value) =>
                {
                    // `{$|x|^(2 n) = x^(2 n)$}`
                    if let Some(arg) = fun.get_arg::<Self>() {
                        return arg.pow(exponant);
                    }
                }
                (Term::Pow(base), Term::Value(exponant))
                    if base.exponant.to_i64().is_some_and(|n| n % 2 == 0)
                        && exponant.value.denominator_ref().even() =>
                {
                    // `{$(x^(2 n))^(p/q) = |x|^(2 n p/q)$}` for even `q`, the root of a positive number being positive
                    return self
                        .fun(Context::ABS, (*base.base).clone())
                        .pow(&(&**base.exponant * &Term::Value(exponant.clone())));
                }
                (Term::Pow(base), Term::Value(exponant)) => {
                    let (numerator, denominator) = exponant.value.to_numerator_and_denominator();
                    let mut res = base.clone();

                    // Numerator and sign can always be passed to the product
                    // If denominator is odd, we can pass it to the product too
                    let (passed_denominator, denominator) = if denominator.odd() {
                        (denominator, Natural::ONE)
                    } else {
                        (Natural::ONE, denominator)
                    };
                    let mul = term::Mul::new(
                        Rational::from_sign_and_naturals(
                            exponant.value.sign() == Ordering::Greater,
                            numerator,
                            passed_denominator,
                        ),
                        vec![(**base.exponant).clone()],
                        self.get_exponant_set(),
                    );

                    let mul = Term::Mul(mul).normalize();
                    let mut res = if mul.is_one() {
                        *res.base.clone()
                    } else if mul.is_zero() {
                        Term::Value(Value::new(Rational::ONE, *self))
                    } else {
                        *res.exponant = mul.into();
                        Term::Pow(res)
                    };
                    if denominator != 1 {
                        res = term::Pow::new(
                            res,
                            Term::Value(Value::new(
                                Rational::from_naturals(Natural::ONE, denominator),
                                *self,
                            )),
                            *self,
                        )
                        .into();
                    }
                    return res;
                }
                (Term::Value(base), Term::Value(exponant))
                    if base.is_approximate() || exponant.is_approximate() =>
                {
                    // Powers of approximations are approximated
                    if let Some(res) = approx::approximate(&a, approx::precision(&base.value)) {
                        return approx::approximate_value(res);
                    }
                }
                (Term::Value(base), Term::Value(exponant)) => {
                    let exponant = &exponant.value;
                    let mut res = base.value.clone();
                    if exponant.sign() == Ordering::Less {
                        if res == 0 {
                            // Division by zero, keep the expression unevaluated
                            return a;
                        }
                        res = Pow::pow(res, -1_i64);
                    }
                    let (mut num, den) = exponant.to_numerator_and_denominator();
                    if let Ok(exponant) = i64::try_from(&num) {
                        res = Pow::pow(res, exponant);
                        num = Natural::ONE;
                        if let Ok(root_exponant) = i64::try_from(&den)
                            && let Some(root_free) = (&res).checked_root(root_exponant)
                        {
                            res = root_free;
                            return Term::Value(Value::new(res, *self));
                        }
                    }
                    if num == 1
                        && res > 0
                        && let Ok(root_exponant) = u64::try_from(&den)
                    {
                        // `{$(s^q r)^(1/q) = s r^(1/q)$}`
                        let (sn, rn) = Self::extract_power(res.numerator_ref(), root_exponant);
                        let (sd, rd) = Self::extract_power(res.denominator_ref(), root_exponant);
                        if sn != 1 || sd != 1 {
                            let root =
                                Term::Value(Value::new(Rational::from_naturals(rn, rd), *self))
                                    .pow(&Term::Value(Value::new(
                                        Rational::from_naturals(Natural::ONE, den),
                                        *self,
                                    )));
                            return Term::Value(Value::new(Rational::from_naturals(sn, sd), *self))
                                * root;
                        }
                    }
                    return Term::Pow(term::Pow::new(
                        Term::Value(Value::new(res, *self)),
                        Term::Value(Value::new(Rational::from_naturals(num, den), *self)),
                        *self,
                    ));
                }
                _ => {}
            },
            Term::Mul(mul) => {
                if let Some(res) = self.merge_radicals(mul) {
                    return res;
                }
            }
            Term::Fun(fun) => match fun.get_ident() {
                Context::ABS => {
                    if let Some(res) = fun.get_arg::<Self>().and_then(|arg| self.eval_abs(arg)) {
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
                Context::LIM => {
                    if let Some([f, Term::Symbol(x), point, direction @ ..]) =
                        fun.get_args::<Self>().map(Vec::as_slice)
                        && let Some(direction) = Direction::from_args(direction)
                    {
                        match f.limit(x.symbol, point, direction) {
                            Ok(res) => return res,
                            Err(LimitError::Undefined) => {
                                return Term::Symbol(SymbolTerm::new(Context::UNDEFINED, *self));
                            }
                            Err(_) => {}
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
                Context::APPROX => {
                    if let Some(res) = fun
                        .get_args::<Self>()
                        .and_then(|args| Self::eval_approx(args))
                    {
                        return res;
                    }
                }
                ident => {
                    if let Some(args) = fun.get_args::<Self>() {
                        // Functions of approximations are approximated, like `{$sin(1.0)$}`
                        let precision = args
                            .iter()
                            .filter_map(|arg| match arg {
                                Term::Value(value) if value.is_approximate() => {
                                    Some(approx::precision(&value.value))
                                }
                                _ => None,
                            })
                            .max();
                        if let Some(precision) = precision
                            && args.iter().all(|arg| matches!(arg, Term::Value(_)))
                            && let Some(res) = approx::approximate(&a, precision)
                        {
                            return approx::approximate_value(res);
                        }
                        if let Some(res) = self.eval_builtin(ident, args) {
                            return res;
                        }
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
        match &a {
            Term::Pow(term::Pow { base, exponant, .. }) => {
                if let (Term::Add(add), Term::Value(value)) = (&**base, &***exponant) {
                    if value.value.denominator_ref() == &Natural::ONE
                        && value.value.numerator_ref() != &Natural::ONE
                        && let Ok(num) = usize::try_from(value.value.numerator_ref())
                    {
                        let terms = Term::expand_sum_power(add, num, Rational::from);
                        if value.value.sign() == Ordering::Less {
                            return term::Pow::new(
                                terms,
                                Term::Value(Value::new(Rational::NEGATIVE_ONE, *self)),
                                *self,
                            )
                            .into();
                        }
                        return terms;
                    }
                } else if let Term::Mul(mul) = &**base {
                    return Term::distribute_pow(mul, exponant);
                }
                a
            }
            _ => a,
        }
    }
}

impl R<Rational> {
    /// Build the function `ident(arg)`, normalized.
    fn fun(self, ident: Symbol, arg: Term<Self>) -> Term<Self> {
        Term::Fun(Box::new(Fun::new(ident, vec![arg], self))).normalize()
    }

    /// Write `{$n = s^q r$}`, returning `(s, r)`. Only prime factors below a bound are extracted, to keep it cheap
    /// on large numbers.
    fn extract_power(n: &Natural, q: u64) -> (Natural, Natural) {
        const BOUND: u64 = 1 << 16;
        let mut s = Natural::ONE;
        let mut r = n.clone();
        let mut p = 2;
        while p < BOUND {
            let power = Pow::pow(Natural::from(p), q);
            if power > r {
                break;
            }
            while (&r % &power) == 0 {
                r /= &power;
                s *= Natural::from(p);
            }
            p += if p == 2 { 1 } else { 2 };
        }
        (s, r)
    }

    /// Merge positive constant radicals with the same exponant in a product, `{$2^(1/2) 3^(1/2) = 6^(1/2)$}`.
    ///
    /// Returns `None` if nothing can be merged.
    fn merge_radicals(self, mul: &term::Mul<Self>) -> Option<Term<Self>> {
        let mut radicals: Vec<(&Rational, Rational)> = vec![];
        let mut rest = vec![];
        let mut merged = false;
        for factor in mul {
            if let Term::Pow(pow) = factor
                && let (Term::Value(base), Term::Value(exponant)) = (&*pow.base, &**pow.exponant)
                && base.value > 0
            {
                if let Some((_, product)) = radicals.iter_mut().find(|(e, _)| **e == exponant.value)
                {
                    *product *= &base.value;
                    merged = true;
                } else {
                    radicals.push((&exponant.value, base.value.clone()));
                }
            } else {
                rest.push(factor.clone());
            }
        }
        if !merged {
            return None;
        }
        let value = |value| Term::Value(Value::new(value, self));
        Some(
            radicals
                .into_iter()
                .map(|(exponant, base)| value(base).pow(&value(exponant.clone())))
                .chain(rest)
                .fold(value(mul.coefficient.clone()), |res, factor| res * factor),
        )
    }

    /// Check if `a` is an even integer
    fn is_even_integer(a: &Rational) -> bool {
        a.denominator_ref() == &1 && a.numerator_ref().even()
    }

    /// Evaluate `|x|`, returning `None` if it can't be simplified.
    fn eval_abs(self, x: &Term<Self>) -> Option<Term<Self>> {
        if x.is_positive() {
            return Some(x.clone());
        }
        if x.is_strictly_negative() {
            return Some(-x);
        }
        match x {
            // `{$||x|| = |x|$}`
            Term::Fun(fun) if fun.get_ident() == Context::ABS => Some(x.clone()),
            // `{$|c x y| = |c| |x| |y|$}`
            Term::Mul(mul) => Some(mul.iter().fold(
                Term::Value(Value::new((&mul.coefficient).abs(), self)),
                |res, factor| res * self.fun(Context::ABS, factor.clone()),
            )),
            Term::Pow(pow) => match &**pow.exponant {
                // `{$|x^(2 n)| = x^(2 n)$}`, and `{$x^(p/q)$}` is positive for even `q`
                Term::Value(exponant)
                    if Self::is_even_integer(&exponant.value)
                        || exponant.value.denominator_ref().even() =>
                {
                    Some(x.clone())
                }
                // `{$|x^n| = |x|^n$}`
                Term::Value(exponant) if exponant.value.denominator_ref() == &1 => Some(
                    self.fun(Context::ABS, (*pow.base).clone())
                        .pow(&pow.exponant),
                ),
                _ => None,
            },
            _ => None,
        }
    }

    /// Over the rationals, `{$gcd(a/b, c/d) = gcd(a, c)/lcm(b, d)$}`
    pub(crate) fn gcd_rational(a: &Rational, b: &Rational) -> Rational {
        let (an, ad) = a.numerator_and_denominator_ref();
        let (bn, bd) = b.numerator_and_denominator_ref();
        Rational::from_naturals(an.gcd(bn), ad.lcm(bd))
    }

    /// Evaluate the builtin function `ident` on `args`, returning `None` if it can't be evaluated.
    /// Evaluate `approx(x)` or `approx(x, digits)`, returning `None` if `digits` isn't a valid number of digits.
    fn eval_approx(args: &[Term<Self>]) -> Option<Term<Self>> {
        let (x, digits) = match args {
            [x] => (x, approx::DEFAULT_DIGITS),
            [x, Term::Value(digits)] => (x, u64::try_from(&digits.value).ok()?),
            _ => return None,
        };
        (1..=approx::MAX_DIGITS)
            .contains(&digits)
            .then(|| approx::approximate_term(x, digits))
    }

    fn eval_builtin(self, ident: Symbol, args: &[Term<Self>]) -> Option<Term<Self>> {
        let value = |value| Term::Value(Value::new(value, self));
        match (ident, args) {
            (Context::EXP | Context::COS, [x]) if x.is_zero() => Some(value(Rational::ONE)),
            (Context::SIN | Context::TAN, [x]) if x.is_zero() => Some(value(Rational::ZERO)),
            (Context::LN, [x]) if x.is_one() => Some(value(Rational::ZERO)),
            (Context::LN, [Term::Symbol(x)]) if x.symbol == Context::E => {
                Some(value(Rational::ONE))
            }
            // `{$e^(ln c) = c$}` for a positive constant `c`
            (Context::EXP, [Term::Fun(inner)])
                if inner.get_ident() == Context::LN
                    && inner.get_arg::<Self>().is_some_and(|arg| {
                        matches!(arg, Term::Value(_)) && arg.is_strictly_positive()
                    }) =>
            {
                inner.get_arg::<Self>().cloned()
            }
            // `{$ln(e^u) = u$}` for a real `u`
            (Context::LN, [Term::Fun(inner)]) if inner.get_ident() == Context::EXP => {
                inner.get_arg::<Self>().cloned()
            }
            (Context::SQRT, [x]) => Some(x.pow(&value(Rational::from_signeds(1, 2)))),
            (Context::ROOT, [x, n]) => Some(x.pow(&n.inv())),
            (Context::SIGN, [x]) => PartialOrd::partial_cmp(x, &Term::zero(self))
                .map(|sign| value(Rational::from(sign as i8))),
            // `{$floor(ceil(x)) = ceil(x)$}`, the inner result is already an integer
            (Context::FLOOR | Context::CEIL, [x @ Term::Fun(inner)])
                if matches!(inner.get_ident(), Context::FLOOR | Context::CEIL) =>
            {
                Some(x.clone())
            }
            (Context::FLOOR, [Term::Value(x)]) => Some(value(Rational::from((&x.value).floor()))),
            (Context::CEIL, [Term::Value(x)]) => Some(value(Rational::from((&x.value).ceiling()))),
            (Context::MIN | Context::MAX, args) => self.eval_extremum(ident, args),
            (Context::GCD, [Term::Value(a), Term::Value(b)]) => {
                Some(value(Self::gcd_rational(&a.value, &b.value)))
            }
            (Context::LCM, [Term::Value(a), Term::Value(b)]) => {
                // Over the rationals, `{$lcm(a/b, c/d) = lcm(a, c)/gcd(b, d)$}`
                let (an, ad) = a.value.numerator_and_denominator_ref();
                let (bn, bd) = b.value.numerator_and_denominator_ref();
                Some(value(Rational::from_naturals(an.lcm(bn), ad.gcd(bd))))
            }
            (Context::GCD | Context::LCM, [a, b]) => {
                let (a, b) = (a.to_polynomial(), b.to_polynomial());
                let gcd = a.gcd(&b);
                if ident == Context::GCD {
                    Some(gcd.to_term())
                } else if a.is_zero() || b.is_zero() {
                    Some(Term::zero(self))
                } else {
                    Some((a.exact_div(&gcd)? * b).monic().to_term())
                }
            }
            _ => None,
        }
    }

    /// Evaluate `min(args)` or `max(args)`, merging every constant argument into one.
    fn eval_extremum(self, ident: Symbol, args: &[Term<Self>]) -> Option<Term<Self>> {
        let keep = if ident == Context::MIN {
            Ordering::Less
        } else {
            Ordering::Greater
        };
        let mut extremum: Option<&Term<Self>> = None;
        let mut rest: Vec<Term<Self>> = vec![];
        for arg in args {
            if let Term::Value(_) = arg {
                if extremum.is_none_or(|e| PartialOrd::partial_cmp(arg, e) == Some(keep)) {
                    extremum = Some(arg);
                }
            } else if !rest.contains(arg) {
                rest.push(arg.clone());
            }
        }
        if rest.is_empty() || (extremum.is_none() && rest.len() == 1) {
            return extremum.cloned().or_else(|| rest.pop());
        }
        rest.extend(extremum.cloned());
        if rest.len() == args.len() {
            // Nothing was merged, keep the original term to avoid normalizing forever
            return None;
        }
        Some(Term::Fun(Box::new(Fun::new(ident, rest, self))))
    }
}

impl SetParseExpression for R<Rational> {
    type MatrixArgumentSet = M<TermSet<Self>>;

    fn get_matrix_argument_set(&self) -> Self::MatrixArgumentSet {
        self.get_term_set().get_matrix_set()
    }

    fn parse_literal(&self, parser: &mut Parser) -> Result<Option<Self::Element>, String> {
        parser.is_literal_and(|value| {
            Ok(Some(Rational::from_sci_string(value).ok_or_else(|| {
                format!("Failed to parse \"{value}\" to malachite::Integer",)
            })?))
        })
    }
}

impl Field for R<Rational> {}

impl Derivable for R<Rational> {
    fn derivative(&self, _: &Self::Element, _: Symbol) -> Self::Element {
        Rational::ZERO
    }
}

/// The real field, using [`malachite::rational::Rational`] as constants to get arbitrary precision numbers.
pub const R: R<Rational> = R {
    phantom: PhantomData,
};
