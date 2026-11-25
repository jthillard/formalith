//! The real field `{$RR$}`.

pub(crate) mod approx;
pub(crate) mod expr;
pub mod numeric;
mod rewrite;
pub(crate) mod rootof;
pub(crate) mod sign;
pub(crate) mod special;

use std::{cmp::Ordering, marker::PhantomData};

use malachite::{
    Integer, Natural, Rational,
    base::num::{
        arithmetic::traits::{
            Abs, BinomialCoefficient, Ceiling, CheckedRoot, CheckedSqrt, Factorial, Floor, Gcd,
            Lcm, Parity, Pow, Reciprocal, Sign,
        },
        basic::traits::{NegativeOne, One, Zero},
    },
};

use super::{parse_rational_literal, primes};
use sign::SignMode;

use crate::term::fun::{
    degree_args, degree_exponents, eval_algebra_builtin, eval_calculus_builtin, eval_matrix_builtin,
};
use crate::{
    context::{
        Context, Symbol,
        assumptions::{SignSet, assumption},
    },
    field::{
        Derivable, Field, Group, Monoid, PartiallyOrderedSet, Ring, Semiring, Set,
        SetParseExpression, matrix::M,
    },
    integrate::{IntegrateError, apart_arguments},
    limit::{Direction, LimitError, remainder},
    parser::Parser,
    polynom::ToTerm,
    printer::PrettyPrinter,
    sum::SumError,
    term::{self, Fun, Normalize, SymbolTerm, Term, TermSet, Value, flags::Flags},
};

/// Largest `n` for which `{$n!$}` is evaluated, to avoid huge computations.
pub(crate) const MAX_FACTORIAL: u64 = 100_000;
/// Maximum exponent tried when evaluating `{$log_b(x)$}` as an integer.
const MAX_LOG_ITERATIONS: i64 = 4096;

/// The real field `{$RR$}` with rational values, the type of [`R`].
pub type Real = R<Rational>;

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

impl Monoid for R<Rational> {
    fn zero(&self) -> Self::Element {
        Rational::ZERO
    }

    fn add(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        a + b
    }

    fn to_i64(&self, a: &Self::Element) -> Option<i64> {
        i64::try_from(a).ok()
    }
}

impl Group for R<Rational> {
    fn nth(&self, nth: i64) -> <Self::ProductCoefficientSet as Set>::Element {
        Rational::const_from_signed(nth)
    }

    fn neg(&self, a: &Self::Element) -> Self::Element {
        -a
    }
}

impl Semiring for R<Rational> {
    fn one(&self) -> Self::Element {
        Rational::ONE
    }

    fn mul(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        a * b
    }

    fn normalize(&self, a: Term<Self>) -> Term<Self> {
        if let Some(res) = self.eval_infinite(&a) {
            return res;
        }
        match &a {
            Term::Pow(term::Pow { base, exponant, .. }) => match (&**base, &***exponant) {
                (Term::Value(minus_one), exponant)
                    if minus_one.value == -1
                        && !matches!(exponant, Term::Value(_))
                        && let Some(exponant) = Self::reduce_parity(exponant) =>
                {
                    // `{$(-1)^(2 k + 1) = -1$}`, `{$(-1)^(3 n) = (-1)^n$}` for integers `k`, `n`
                    return self.value(Rational::NEGATIVE_ONE).pow(&exponant);
                }
                (Term::Symbol(e), _) if e.symbol == Context::E => {
                    // `{$e^u = exp u$}`, a single form for exponentials
                    return self.fun(Context::EXP, (***exponant).clone());
                }
                (Term::Mul(mul), Term::Value(value)) if value.value.denominator_ref() == &1 => {
                    // `{$(x y)^n = x^n y^n$}` for integer `n`
                    return Term::distribute_pow(mul, exponant);
                }
                (Term::Mul(mul), Term::Value(_))
                    if mul.coefficient > 0
                        && mul.coefficient != 1
                        && matches!(
                            self.value(mul.coefficient.clone()).pow(exponant),
                            Term::Value(_)
                        ) =>
                {
                    // `{$(c u)^e = c^e u^e$}` for `{$c > 0$}` when `{$c^e$}` is rational, `{$sqrt(4 x^2) = 2 |x|$}`
                    let rest = mul.iter().fold(self.value(Rational::ONE), |res, f| res * f);
                    return self.value(mul.coefficient.clone()).pow(exponant) * rest.pow(exponant);
                }
                (Term::Add(add), Term::Value(value))
                    if value.value.denominator_ref().odd()
                        && value.value.denominator_ref() != &1u32
                        && add.iter().all(|term| match term {
                            Term::Mul(mul) => mul.coefficient < 0,
                            Term::Value(v) => v.value < 0,
                            _ => false,
                        }) =>
                {
                    // The same for sums of negative terms, `{$(-x^3 - x)^(1/3) = -(x^3 + x)^(1/3)$}` (not for others,
                    // `{$(1 - x)^(1/3)$}` staying a root of a positive base near 0)
                    let sign = if value.value.numerator_ref().odd() {
                        Rational::NEGATIVE_ONE
                    } else {
                        Rational::ONE
                    };
                    // Term by term, `{$-1 dot (...)$}` being turned back into this sum by the rule below
                    let positive = add
                        .iter()
                        .fold(self.value(Rational::ZERO), |res, term| res - term);
                    return self.value(sign) * positive.pow(exponant);
                }
                (Term::Mul(mul), Term::Value(value))
                    if mul.coefficient < 0 && value.value.denominator_ref().odd() =>
                {
                    // `{$(-u)^(p/q) = (-1)^p u^(p/q)$}` for odd `q`, roots of odd order being real, so that
                    // `{$(-x)^(1/3) = -x^(1/3)$}`
                    let sign = if value.value.numerator_ref().odd() {
                        Rational::NEGATIVE_ONE
                    } else {
                        Rational::ONE
                    };
                    let positive = -Term::Mul(mul.clone());
                    return self.value(sign) * positive.pow(exponant);
                }
                (Term::Add(add), Term::Value(exponant))
                    if exponant.value == Rational::from_signeds(1, 2)
                        && let Some(res) = self.denest(add) =>
                {
                    return res;
                }
                (Term::Mul(mul), Term::Value(_))
                    if mul.coefficient > 0 && mul.iter().all(Self::is_positive_constant) =>
                {
                    // `{$(2 pi)^(1/2) = 2^(1/2) pi^(1/2)$}`, a single form for roots of positive constants
                    return Term::distribute_pow(mul, exponant);
                }
                (Term::Fun(fun), Term::Value(n))
                    if fun.get_ident() == Context::real_root()
                        && let Some(args) = fun.get_args::<Self>()
                        && let Some(res) = rootof::reduce_power(base, args, &n.value) =>
                {
                    // `{$alpha^n$}` reduced modulo the polynomial of a root `{$alpha$}`
                    return res;
                }
                (Term::Fun(fun), _) if fun.get_ident() == Context::EXP => {
                    // `{$(exp u)^c = exp(c u)$}`, `{$exp u$}` being positive
                    if let Some(arg) = fun.get_arg::<Self>() {
                        return self.fun(Context::EXP, arg * &***exponant);
                    }
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
                            && (res >= 0 || root_exponant % 2 != 0)
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
                        if sn != 1 || sd != 1 || rd != 1 {
                            // `{$(a/b)^(1/q) = (a b^(q-1))^(1/q) / b$}`
                            let (rn, sd) = if rd == 1 {
                                (rn, sd)
                            } else {
                                (rn * Pow::pow(rd.clone(), root_exponant - 1), sd * rd)
                            };
                            let root = Term::Value(Value::new(
                                Rational::from_naturals(rn, Natural::ONE),
                                *self,
                            ))
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
                if mul.iter().any(|factor| matches!(factor, Term::Value(_))) {
                    // Merged factors may be values (`{$x x^(-1) = 1$}`, `{$sqrt(2) sqrt(2) = 2$}`), moved to the
                    // coefficient
                    let mut res = Term::Value(Value::new(mul.coefficient.clone(), *self));
                    res.set_approximate(mul.is_approximate());
                    for factor in mul {
                        res *= factor;
                    }
                    return res;
                }
                let is_exp = |factor: &&Term<Self>| matches!(factor, Term::Fun(fun) if fun.get_ident() == Context::EXP);
                if mul.iter().filter(is_exp).count() > 1 {
                    // `{$exp(a) exp(b) = exp(a + b)$}`, so that exponentials cancel like powers of a single base
                    let mut res = Term::Value(Value::new(mul.coefficient.clone(), *self));
                    res.set_approximate(mul.is_approximate());
                    let mut argument = Term::zero(*self);
                    for factor in mul {
                        match factor {
                            Term::Fun(fun) if fun.get_ident() == Context::EXP => {
                                if let Some(arg) = fun.get_arg::<Self>() {
                                    argument += arg;
                                }
                            }
                            _ => res *= factor,
                        }
                    }
                    return res * self.fun(Context::EXP, argument);
                }
                if let Some(res) = self.merge_radicals(mul) {
                    return res;
                }
                let is_little_o = |factor: &&Term<Self>| matches!(factor, Term::Fun(fun) if fun.get_ident() == Context::LITTLE_O);
                if mul.iter().any(|factor| is_little_o(&factor)) {
                    // `{$f o(u) = o(f u)$}` and `{$o(u) o(v) = o(u v)$}`
                    let mut res = Term::Value(Value::new(mul.coefficient.clone(), *self));
                    for factor in mul {
                        match factor {
                            Term::Fun(fun) if fun.get_ident() == Context::LITTLE_O => {
                                if let Some(arg) = fun.get_arg::<Self>() {
                                    res *= arg;
                                }
                            }
                            _ => res *= factor,
                        }
                    }
                    return self.fun(Context::LITTLE_O, res);
                }
            }
            Term::Fun(fun) => match fun.get_ident() {
                Context::LITTLE_O => {
                    // `{$o(c u) = o(u)$}` for a non-zero constant `c`
                    match fun.get_arg::<Self>() {
                        Some(Term::Value(c)) if c.value != 0 && c.value != 1 => {
                            return self.fun(Context::LITTLE_O, self.value(Rational::ONE));
                        }
                        Some(Term::Mul(mul)) if mul.coefficient != 1 && mul.coefficient != 0 => {
                            return self.fun(
                                Context::LITTLE_O,
                                Term::Mul(mul.clone()) / self.value(mul.coefficient.clone()),
                            );
                        }
                        _ => {}
                    }
                }
                Context::ARG => {
                    if let Some(res) = fun
                        .get_arg::<Self>()
                        .and_then(|arg| expr::arg(arg, &expr::zero()))
                    {
                        return res;
                    }
                }
                Context::ABS => {
                    if let Some(res) = fun.get_arg::<Self>().and_then(|arg| self.eval_abs(arg)) {
                        return res;
                    }
                }
                Context::EXPAND => {
                    if let Some(arg) = fun.get_arg::<Self>() {
                        return rewrite::expand(arg);
                    }
                }
                Context::SIMPLIFY => {
                    if let Some(arg) = fun.get_arg::<Self>() {
                        return rewrite::simplify(arg);
                    }
                }
                Context::FACTOR => {
                    if let Some(arg) = fun.get_arg::<Self>() {
                        return arg.factor();
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
                    if let Some(res) = self.eval_degree(&**fun) {
                        return res;
                    }
                }
                // Also in exponents, unlike other rings
                Context::SUBS => {
                    if let Some([f, Term::Symbol(x), a]) = fun.get_args::<Self>().map(Vec::as_slice)
                    {
                        return expr::subs(f, x.symbol, a);
                    }
                }
                Context::NUMER | Context::DENOM | Context::RESULTANT | Context::DISCRIMINANT => {
                    if let Some(res) = eval_algebra_builtin(&**fun) {
                        return res;
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
                Context::SERIES => {
                    if let Some([f, Term::Symbol(x), point, rest @ ..]) =
                        fun.get_args::<Self>().map(Vec::as_slice)
                    {
                        if let [Term::Symbol(oo), direction @ ..] = rest
                            && oo.symbol == Context::OO
                        {
                            if let Some(direction) = Direction::from_args(direction)
                                && let Ok(res) = f.infinite_series(x.symbol, point, direction)
                            {
                                return res;
                            }
                            return a;
                        }
                        let (order, direction) = match rest {
                            [] => (Some(Rational::from(6)), Some(Direction::Both)),
                            [Term::Value(order), direction @ ..] => {
                                (Some(order.value.clone()), Direction::from_args(direction))
                            }
                            _ => (None, None),
                        };
                        if let (Some(order), Some(direction)) = (order, direction)
                            && let Ok(res) = f.series(x.symbol, point, &order, direction)
                        {
                            return res + remainder(x.symbol, point, &order);
                        }
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
                Context::INTEGRATE => {
                    let res = match fun.get_args::<Self>().map(Vec::as_slice) {
                        Some([f, Term::Symbol(x)]) => f.integrate(x.symbol),
                        Some([f, Term::Symbol(x), a, b]) => f.integrate_definite(x.symbol, a, b),
                        _ => Err(IntegrateError::Unsupported),
                    };
                    match res {
                        Ok(res) => return res,
                        Err(IntegrateError::Divergent(sign)) => {
                            let oo = Term::Symbol(SymbolTerm::new(Context::OO, *self));
                            return if sign == Ordering::Less { -oo } else { oo };
                        }
                        Err(IntegrateError::Undefined) => {
                            return Term::Symbol(SymbolTerm::new(Context::UNDEFINED, *self));
                        }
                        Err(IntegrateError::Unsupported | IntegrateError::NonElementary) => {}
                    }
                }
                Context::SUM | Context::PRODUCT => {
                    if let Some([f, Term::Symbol(k), a, b]) =
                        fun.get_args::<Self>().map(Vec::as_slice)
                    {
                        let res = if fun.get_ident() == Context::SUM {
                            f.sum(k.symbol, a, b)
                        } else {
                            f.product(k.symbol, a, b)
                        };
                        match res {
                            Ok(res) => return res,
                            Err(SumError::Divergent(sign)) => {
                                let oo = Term::Symbol(SymbolTerm::new(Context::OO, *self));
                                return if sign == Ordering::Less { -oo } else { oo };
                            }
                            Err(SumError::Undefined) => {
                                return Term::Symbol(SymbolTerm::new(Context::UNDEFINED, *self));
                            }
                            Err(SumError::Unsupported) => {}
                        }
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
                } else if let Term::Mul(mul) = &**base
                    // `{$(-x)^(1/2)$}` isn't `{$(-1)^(1/2) x^(1/2)$}` in `{$RR$}`
                    && (mul.coefficient > 0
                        || matches!(&***exponant, Term::Value(value)
                            if value.value.denominator_ref() == &1))
                {
                    return Term::distribute_pow(mul, exponant);
                }
                a
            }
            _ => a,
        }
    }
}

impl Ring for R<Rational> {
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
}

impl R<Rational> {
    /// The constant `value`.
    const fn value(self, value: Rational) -> Term<Self> {
        Term::Value(Value::new(value, self))
    }

    /// Denest `{$sqrt(a + b sqrt(c)) = sqrt((a + d)/2) + "sign"(b) sqrt((a - d)/2)$}` for rationals `a`, `b` and `c`,
    /// when `{$d^2 = a^2 - b^2 c$}` is the square of a rational `d`.
    fn denest(self, add: &term::Add<Self>) -> Option<Term<Self>> {
        let (a, radical) = match add.iter().collect::<Vec<_>>().as_slice() {
            [Term::Value(a), radical] | [radical, Term::Value(a)] => (a.value.clone(), *radical),
            _ => return None,
        };
        let (b, radical) = match radical {
            Term::Mul(mul) => match mul.iter().collect::<Vec<_>>().as_slice() {
                [radical] => (mul.coefficient.clone(), *radical),
                _ => return None,
            },
            _ => (Rational::ONE, radical),
        };
        let Term::Pow(pow) = radical else { return None };
        let (Term::Value(c), Term::Value(half)) = (&*pow.base, &**pow.exponant) else {
            return None;
        };
        if half.value != Rational::from_signeds(1, 2) || a <= 0 || add.is_approximate() {
            return None;
        }
        let square = &a * &a - &b * &b * &c.value;
        if square < 0 {
            return None;
        }
        let d = (&square).checked_sqrt()?;
        let two = Rational::from(2);
        let root = |x: Rational| self.value(x).pow(&self.value(Rational::from_signeds(1, 2)));
        let (plus, minus) = (root((&a + &d) / &two), root((&a - &d) / &two));
        Some(if b > 0 { plus + minus } else { plus - minus })
    }

    /// Build the function `ident(arg)`, normalized.
    fn fun(self, ident: Symbol, arg: Term<Self>) -> Term<Self> {
        Term::Fun(Box::new(Fun::new(ident, vec![arg], self))).normalize()
    }

    /// Arithmetic with `{$oo$}`: `{$oo + c = oo$}` for a constant `c`, `{$oo - oo = "undefined"$}`, `{$c oo = oo$}` for a positive
    /// constant `c`, `{$oo^n = oo$}` for `{$n > 0$}` and `{$oo^n = 0$}` for `{$n < 0$}`. `undefined` absorbs sums and
    /// products. Returns `None` when nothing applies.
    fn eval_infinite(self, a: &Term<Self>) -> Option<Term<Self>> {
        let oo = || Term::Symbol(SymbolTerm::new(Context::OO, self));
        let undefined = || Term::Symbol(SymbolTerm::new(Context::UNDEFINED, self));
        let is_undefined =
            |t: &Term<Self>| matches!(t, Term::Symbol(s) if s.symbol == Context::UNDEFINED);
        match a {
            Term::Pow(pow) if matches!(&*pow.base, Term::Symbol(s) if s.symbol == Context::OO) => {
                match &**pow.exponant {
                    Term::Value(n) if n.value > 0 => Some(oo()),
                    Term::Value(n) if n.value < 0 => Some(Term::zero(self)),
                    _ => None,
                }
            }
            Term::Add(add) => {
                if add.iter().any(is_undefined) {
                    return Some(undefined());
                }
                let (mut positive, mut negative) = (false, false);
                for term in add {
                    if term.is_infinity_factor() {
                        match term {
                            Term::Mul(mul) if mul.coefficient < 0 => negative = true,
                            _ => positive = true,
                        }
                    } else if term
                        .symbols()
                        .iter()
                        .any(|s| *s == Context::OO || !Context::is_builtin_constant(*s))
                    {
                        // Only finite constants are dropped, `{$x + oo$}` is kept
                        return None;
                    }
                }
                match (positive, negative) {
                    (true, true) => Some(undefined()),
                    (true, false) => Some(oo()),
                    (false, true) => Some(-oo()),
                    (false, false) => None,
                }
            }
            Term::Mul(mul) => {
                if mul.iter().any(is_undefined) {
                    return Some(undefined());
                }
                let (infinite, rest): (Vec<_>, Vec<_>) =
                    mul.iter().partition(|factor| factor.is_infinity_factor());
                // `{$-oo$}` is already normalized
                let normalized =
                    infinite.len() == 1 && rest.is_empty() && (&mul.coefficient).abs() == 1;
                if infinite.is_empty()
                    || normalized
                    || !infinite.iter().all(|factor| **factor == oo())
                    || !rest.into_iter().all(Self::is_positive_constant)
                {
                    return None;
                }
                Some(if mul.coefficient > 0 { oo() } else { -oo() })
            }
            _ => None,
        }
    }

    /// Whether `term` is a positive constant: a positive value, `{$pi$}`, `{$e$}`, a symbol assumed positive, or
    /// a power of one of them.
    fn is_positive_constant(term: &Term<Self>) -> bool {
        match term {
            Term::Value(value) => value.value > 0,
            Term::Symbol(symbol) => {
                matches!(
                    symbol.symbol,
                    Context::PI | Context::E | Context::EULER_GAMMA
                ) || assumption(symbol.symbol).sign == SignSet::POSITIVE
            }
            Term::Pow(pow) => {
                matches!(&**pow.exponant, Term::Value(_)) && Self::is_positive_constant(&pow.base)
            }
            _ => false,
        }
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

    /// Whether `x` is non-negative for every value of its symbols, checked on positive constants, `exp`, `cosh`,
    /// even powers, roots, and sums and products of such terms.
    pub(crate) fn is_non_negative(x: &Term<Self>) -> bool {
        match x {
            Term::Value(_) => x.is_positive(),
            Term::Symbol(s) => matches!(s.symbol, Context::PI | Context::E | Context::EULER_GAMMA),
            Term::Add(add) => add.iter().all(Self::is_non_negative),
            Term::Mul(mul) => mul.coefficient >= 0 && mul.iter().all(Self::is_non_negative),
            Term::Pow(pow) => match &**pow.exponant {
                Term::Value(exponant)
                    if Self::is_even_integer(&exponant.value)
                        || exponant.value.denominator_ref().even() =>
                {
                    true
                }
                _ => Self::is_non_negative(&pow.base),
            },
            Term::Fun(fun) => matches!(
                fun.get_ident(),
                Context::EXP | Context::COSH | Context::ABS | Context::SQRT
            ),
        }
    }

    /// Evaluate `|x|`, returning `None` if it can't be simplified.
    fn eval_abs(self, x: &Term<Self>) -> Option<Term<Self>> {
        let sign = sign::sign_set(x, SignMode::STRUCTURAL);
        if x.is_positive() || Self::is_non_negative(x) || sign.is_subset(SignSet::NONNEGATIVE) {
            return Some(x.clone());
        }
        if sign.is_subset(SignSet::NONPOSITIVE) {
            return Some(-x);
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
        profile_scope!("approx");
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
        if let [x] = args
            && let Some(res) = self
                .eval_parity(ident, x)
                .or_else(|| self.eval_periodicity(ident, x))
                .or_else(|| self.eval_integer_turns(ident, x))
                .or_else(|| self.eval_at_infinity(ident, x))
        {
            return Some(res);
        }
        match (ident, args) {
            (Context::EXP | Context::COS, [x]) if x.is_zero() => Some(value(Rational::ONE)),
            (Context::SIN | Context::TAN, [x]) if x.is_zero() => Some(value(Rational::ZERO)),
            (Context::SIN | Context::COS | Context::TAN, [x]) if Self::pi_multiple(x).is_some() => {
                self.eval_trig_at_pi_multiple(ident, &Self::pi_multiple(x)?)
            }
            (Context::LN, [x]) if x.is_one() => Some(value(Rational::ZERO)),
            // `{$ln q = -ln(1/q)$}` for `{$0 < q < 1$}`
            (Context::LN, [Term::Value(x)]) if x.value > 0 && x.value < 1 => {
                Some(-self.fun(Context::LN, value((&x.value).reciprocal())))
            }
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
            // `{$e^(q ln c) = c^q$}` for a rational `q` and a positive value `c`
            (Context::EXP, [Term::Mul(mul)])
                if let [Term::Fun(inner)] = mul.iter().collect::<Vec<_>>().as_slice()
                    && inner.get_ident() == Context::LN
                    && let Some(c @ Term::Value(_)) = inner.get_arg::<Self>()
                    && c.is_strictly_positive() =>
            {
                Some(c.pow(&value(mul.coefficient.clone())))
            }
            // `{$ln(e^u) = u$}` for a real `u`
            (Context::LN, [Term::Fun(inner)]) if inner.get_ident() == Context::EXP => {
                inner.get_arg::<Self>().cloned()
            }
            (Context::SQRT, [x]) => Some(x.pow(&value(Rational::from_signeds(1, 2)))),
            (Context::ROOT, [x, n]) => Some(x.pow(&n.inv())),
            (Context::SIGN, [x]) => PartialOrd::partial_cmp(x, &Term::zero(self))
                .or_else(|| sign::sign(x, SignMode::STRUCTURAL))
                .map(|sign| value(Rational::from(sign as i8))),
            // `{$floor(n) = n$}` for an integer `n`
            (Context::FLOOR | Context::CEIL, [x]) if sign::is_integer(x) => Some(x.clone()),
            // `{$floor(ceil(x)) = ceil(x)$}`, the inner result is already an integer
            (Context::FLOOR | Context::CEIL, [x @ Term::Fun(inner)])
                if matches!(inner.get_ident(), Context::FLOOR | Context::CEIL) =>
            {
                Some(x.clone())
            }
            (Context::FLOOR, [Term::Value(x)]) => Some(value(Rational::from((&x.value).floor()))),
            (Context::CEIL, [Term::Value(x)]) => Some(value(Rational::from((&x.value).ceiling()))),
            (Context::MIN | Context::MAX, args) => self.eval_extremum(ident, args),
            (Context::SINH | Context::TANH | Context::ASINH | Context::ATANH, [x])
                if x.is_zero() =>
            {
                Some(value(Rational::ZERO))
            }
            (Context::ERF | Context::ERFI | Context::SI, [x]) if x.is_zero() => {
                Some(value(Rational::ZERO))
            }
            // Logarithmic singularities
            (Context::CI | Context::EI, [x]) if x.is_zero() => {
                Some(-Term::Symbol(SymbolTerm::new(Context::OO, self)))
            }
            (Context::COSH, [x]) if x.is_zero() => Some(value(Rational::ONE)),
            (Context::ACOSH, [x]) if x.is_one() => Some(value(Rational::ZERO)),
            (Context::ASIN | Context::ACOS | Context::ATAN, [x]) => {
                if ident == Context::ATAN
                    && let Some(res) = self.eval_atan_of_tan(x)
                {
                    return Some(res);
                }
                self.eval_inverse_trig(ident, x)
            }
            (Context::COT, [x]) => {
                Some(self.fun(Context::COS, x.clone()) / self.fun(Context::SIN, x.clone()))
            }
            (Context::SEC, [x]) => Some(self.fun(Context::COS, x.clone()).inv()),
            (Context::CSC, [x]) => Some(self.fun(Context::SIN, x.clone()).inv()),
            (Context::ERFC, [x]) => Some(value(Rational::ONE) - self.fun(Context::ERF, x.clone())),
            // Halves are rounded up, `{$"round"(x) = floor(x + 1/2)$}`
            (Context::ROUND, [x]) => {
                Some(self.fun(Context::FLOOR, x + &value(Rational::from_signeds(1, 2))))
            }
            (Context::TRUNC, [Term::Value(x)]) => Some(value(if x.value < 0 {
                Rational::from((&x.value).ceiling())
            } else {
                Rational::from((&x.value).floor())
            })),
            (Context::TRUNC, [x]) => Some(
                self.fun(Context::SIGN, x.clone())
                    * self.fun(Context::FLOOR, self.fun(Context::ABS, x.clone())),
            ),
            (Context::ISPRIME, [Term::Value(x)]) => {
                let prime = Natural::try_from(&x.value).is_ok_and(|n| primes::is_prime(&n));
                Some(value(Rational::from(u8::from(prime))))
            }
            (Context::LOG, [x]) => Some(self.eval_log(x, &value(Rational::from(10)))),
            (Context::LOG, [x, base]) => Some(self.eval_log(x, base)),
            // Approximations stay unevaluated, the singular values being exact
            (
                Context::FACTORIAL
                | Context::BINOMIAL
                | Context::GAMMA
                | Context::POLYGAMMA
                | Context::ZETA,
                args,
            ) if args.iter().any(term::flags::Flags::is_approximate) => None,
            (
                Context::GAMMA
                | Context::BETA
                | Context::DIGAMMA
                | Context::POLYGAMMA
                | Context::ZETA
                | Context::BERNOULLI
                | Context::EULER,
                args,
            ) => self.eval_gamma_family(ident, args),
            (Context::LAMBERTW, [x]) if !x.is_approximate() => self.eval_lambertw(x, true),
            // `lambertw(x, k)` for the branches `{$k = 0$}` and `{$k = -1$}`, an internal function
            (Context::LAMBERTW, [x, Term::Value(k)]) if k.value == 0 => {
                Some(self.fun(Context::LAMBERTW, x.clone()))
            }
            (Context::LAMBERTW, [x, Term::Value(k)]) if k.value == -1 => {
                Some(self.fun(Context::lambertw_m1(), x.clone()))
            }
            (ident, [x]) if ident == Context::lambertw_m1() && !x.is_approximate() => {
                self.eval_lambertw(x, false)
            }
            (Context::PIECEWISE, args) => self.eval_piecewise(args),
            (Context::ROOTOF, args) => rootof::eval_rootof(args),
            (Context::FACTORIAL, [Term::Value(n)]) => self.eval_factorial(&n.value),
            (Context::BINOMIAL, [n, Term::Value(k)]) if k.value == 0 || k.value == 1 => {
                Some(if k.value == 0 {
                    value(Rational::ONE)
                } else {
                    n.clone()
                })
            }
            (Context::BINOMIAL, [Term::Value(n), Term::Value(k)]) => {
                let k = Integer::try_from(&k.value).ok()?;
                if k < 0 {
                    return Some(value(Rational::ZERO));
                }
                if let Ok(n) = Natural::try_from(&n.value) {
                    let k = Natural::try_from(k).ok()?;
                    if k > n {
                        return Some(value(Rational::ZERO));
                    }
                    return Some(value(Rational::from(Natural::binomial_coefficient(n, k))));
                }
                // `{$binom(n, k) = (n (n - 1) ... (n - k + 1)) / k!$}`
                let k = u64::try_from(&k).ok().filter(|k| *k <= MAX_FACTORIAL)?;
                let mut res = Rational::ONE;
                for i in 0..k {
                    res *= (&n.value - Rational::from(i)) / Rational::from(i + 1);
                }
                Some(value(res))
            }
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
                Some(if ident == Context::GCD {
                    a.gcd(&b).to_term()
                } else {
                    a.lcm(&b)?.to_term()
                })
            }
            _ => None,
        }
    }

    /// Evaluate `{$n!$}` for a natural `n`, or a half-integer `n` with `{$Gamma(1/2) = sqrt(pi)$}`.
    fn eval_factorial(self, n: &Rational) -> Option<Term<Self>> {
        if let Ok(n) = u64::try_from(n) {
            return (n <= MAX_FACTORIAL).then(|| self.value(Rational::from(Natural::factorial(n))));
        }
        let half = Rational::from_signeds(1, 2);
        // `{$n! = Gamma(x)$}` with `{$x = n + 1$}`, `{$x - 1/2$}` being an integer
        let x = n + Rational::ONE;
        let steps = i64::try_from(&(&x - &half)).ok()?;
        if steps.unsigned_abs() > MAX_FACTORIAL {
            return None;
        }
        // `{$Gamma(t + 1) = t Gamma(t)$}`
        let mut coefficient = Rational::ONE;
        let mut t = half.clone();
        for _ in 0..steps.abs() {
            if steps > 0 {
                coefficient *= &t;
                t += Rational::ONE;
            } else {
                t -= Rational::ONE;
                coefficient /= &t;
            }
        }
        let pi = Term::Symbol(SymbolTerm::new(Context::PI, self));
        Some(self.value(coefficient) * pi.pow(&self.value(half)))
    }

    /// Evaluate `{$log_b(x) = ln(x) / ln(b)$}`, an integer `k` when `{$x = b^k$}` for rational `x` and `b`.
    fn eval_log(self, x: &Term<Self>, base: &Term<Self>) -> Term<Self> {
        if let (Term::Value(x), Term::Value(base)) = (x, base)
            && let Some(k) = Self::integer_log(&x.value, &base.value)
        {
            return Term::Value(Value::new(Rational::from(k), self));
        }
        self.fun(Context::LN, x.clone()) / self.fun(Context::LN, base.clone())
    }

    /// The integer `k` such that `{$x = b^k$}`, if any, for positive `x` and `{$b != 1$}`.
    fn integer_log(x: &Rational, b: &Rational) -> Option<i64> {
        if *x <= 0 || *b <= 0 || *b == 1 {
            return None;
        }
        // `{$log_b(x) = -log_b(1/x) = -log_(1/b)(x)$}`, reduce to `{$x >= 1$}` and `{$b > 1$}`
        let (x, sign) = if *x < 1 {
            (x.reciprocal(), -1)
        } else {
            (x.clone(), 1)
        };
        let (b, sign) = if *b < 1 {
            (b.reciprocal(), -sign)
        } else {
            (b.clone(), sign)
        };
        let mut power = Rational::ONE;
        for k in 0..MAX_LOG_ITERATIONS {
            match power.cmp(&x) {
                Ordering::Equal => return Some(sign * k),
                Ordering::Greater => return None,
                Ordering::Less => power *= &b,
            }
        }
        None
    }

    /// The rational `q` if `x` is `{$q pi$}`.
    fn pi_multiple(x: &Term<Self>) -> Option<Rational> {
        match x {
            Term::Symbol(symbol) if symbol.symbol == Context::PI => Some(Rational::ONE),
            Term::Mul(mul)
                if matches!(mul.iter().collect::<Vec<_>>().as_slice(),
                    [Term::Symbol(symbol)] if symbol.symbol == Context::PI) =>
            {
                Some(mul.coefficient.clone())
            }
            _ => None,
        }
    }

    /// Whether `x` is written with a minus sign: a negative value, or a product with a negative coefficient.
    fn has_minus_sign(x: &Term<Self>) -> bool {
        match x {
            Term::Value(value) => value.value < 0,
            Term::Mul(mul) => mul.coefficient < 0,
            _ => false,
        }
    }

    /// `{$f(-u) = -f(u)$}` for odd functions and `{$f(-u) = f(u)$}` for even ones.
    fn eval_parity(self, ident: Symbol, x: &Term<Self>) -> Option<Term<Self>> {
        if !Self::has_minus_sign(x) {
            return None;
        }
        match ident {
            Context::SIN
            | Context::TAN
            | Context::SINH
            | Context::TANH
            | Context::ASIN
            | Context::ATAN
            | Context::ASINH
            | Context::ATANH
            | Context::SIGN
            | Context::ERF
            | Context::ERFI
            | Context::SI => Some(-self.fun(ident, -x)),
            Context::COS | Context::COSH => Some(self.fun(ident, -x)),
            _ => None,
        }
    }

    /// Reduce the multiples of `{$pi$}` in the argument `{$u + q pi$}` of `sin`, `cos` or `tan`: quarter turns
    /// when `{$2 q$}` is an integer (`{$sin(u + pi) = -sin u$}`, `{$cos(u + pi/2) = -sin u$}`), otherwise half
    /// turns bringing `q` into `{$(-1/2, 1/2)$}` (`{$sin(u + 4 pi/3) = -sin(u + pi/3)$}`).
    fn eval_periodicity(self, ident: Symbol, x: &Term<Self>) -> Option<Term<Self>> {
        if !matches!(ident, Context::SIN | Context::COS | Context::TAN) {
            return None;
        }
        let Term::Add(add) = x else { return None };
        let mut q = Rational::ZERO;
        let mut rest = Term::zero(self);
        let mut found = false;
        for term in add {
            match Self::pi_multiple(term) {
                Some(multiple) => {
                    q += multiple;
                    found = true;
                }
                None => rest += term,
            }
        }
        if !found {
            return None;
        }
        let pi = Term::Symbol(SymbolTerm::new(Context::PI, self));
        let value = |value| Term::Value(Value::new(value, self));
        let half_turns = &q * Rational::from(2);
        if half_turns.denominator_ref() == &1 {
            let quarters = i64::try_from(&half_turns).ok()?.rem_euclid(4);
            let (sin, cos) = (
                || self.fun(Context::SIN, rest.clone()),
                || self.fun(Context::COS, rest.clone()),
            );
            return Some(match (ident, quarters) {
                (Context::SIN, 0) | (Context::COS, 3) => sin(),
                (Context::SIN, 1) | (Context::COS, 0) => cos(),
                (Context::SIN, 2) | (Context::COS, 1) => -sin(),
                (Context::SIN, 3) | (Context::COS, 2) => -cos(),
                (_, 0 | 2) => self.fun(Context::TAN, rest),
                // `{$tan(u + pi/2)$}`, written once with this angle
                _ if q == Rational::from_signeds(1, 2) => return None,
                _ => self.fun(
                    Context::TAN,
                    rest + value(Rational::from_signeds(1, 2)) * pi,
                ),
            });
        }
        // Nearest integer, `q` being at distance at least `{$1/4$}` from a half-integer
        let n = (&q + Rational::from_signeds(1, 2)).floor();
        if n == 0 {
            return None;
        }
        let res = self.fun(ident, rest + value(q - Rational::from(n.clone())) * pi);
        Some(if ident != Context::TAN && n.odd() {
            -res
        } else {
            res
        })
    }

    /// The integer `m` (see [`sign::is_integer`]) with the integer coefficients of its terms reduced modulo 2, the
    /// exponent of `{$(-1)^m$}`, or `None` if `m` isn't an integer or is already reduced.
    fn reduce_parity(m: &Term<Self>) -> Option<Term<Self>> {
        if !sign::is_integer(m) {
            return None;
        }
        let terms: Vec<&Term<Self>> = match m {
            Term::Add(add) => add.iter().collect(),
            _ => vec![m],
        };
        let mut reduced = Term::zero(R);
        let mut changed = false;
        for term in terms {
            let (c, rest) = match term {
                Term::Value(value) => (value.value.clone(), R.value(Rational::ONE)),
                Term::Mul(mul) => (
                    mul.coefficient.clone(),
                    term / &R.value(mul.coefficient.clone()),
                ),
                _ => (Rational::ONE, term.clone()),
            };
            let two = Rational::from(2);
            let r = &c - &two * Rational::from((&c / &two).floor());
            changed |= r != c;
            reduced += R.value(r) * rest;
        }
        changed.then_some(reduced)
    }

    /// Remove the multiples `{$n pi$}` of `{$pi$}` by a symbolic integer `n` (see [`sign::is_integer`]) from the
    /// argument of `sin`, `cos` or `tan`: `{$sin(u + n pi) = (-1)^n sin u$}`, `{$tan(u + n pi) = tan u$}`.
    fn eval_integer_turns(self, ident: Symbol, x: &Term<Self>) -> Option<Term<Self>> {
        if !matches!(ident, Context::SIN | Context::COS | Context::TAN) {
            return None;
        }
        let pi = Term::Symbol(SymbolTerm::new(Context::PI, self));
        // The integer `n` of a term `{$n pi$}`, which isn't a value
        let turns = |term: &Term<Self>| {
            let Term::Mul(mul) = term else { return None };
            if !mul.iter().any(|factor| *factor == pi) {
                return None;
            }
            let n = term / &pi;
            (!matches!(n, Term::Value(_)) && sign::is_integer(&n)).then_some(n)
        };
        let terms: Vec<&Term<Self>> = match x {
            Term::Add(add) => add.iter().collect(),
            _ => vec![x],
        };
        let mut n = Term::zero(self);
        let mut rest = Term::zero(self);
        for term in terms {
            match turns(term) {
                Some(turns) => n += turns,
                None => rest += term,
            }
        }
        if n.is_zero() {
            return None;
        }
        let res = self.fun(ident, rest);
        Some(if ident == Context::TAN {
            res
        } else {
            self.value(Rational::NEGATIVE_ONE).pow(&n) * res
        })
    }

    /// Values of functions at `{$oo$}` and `{$-oo$}`, those at `{$-oo$}` coming from [`Self::eval_parity`] for
    /// odd and even functions.
    fn eval_at_infinity(self, ident: Symbol, x: &Term<Self>) -> Option<Term<Self>> {
        let value = |value| Term::Value(Value::new(value, self));
        let oo = Term::Symbol(SymbolTerm::new(Context::OO, self));
        if *x == -&oo {
            return matches!(ident, Context::EXP | Context::EI).then(|| value(Rational::ZERO));
        }
        if *x != oo {
            return None;
        }
        match ident {
            Context::EXP
            | Context::LN
            | Context::SINH
            | Context::COSH
            | Context::ASINH
            | Context::ACOSH
            | Context::GAMMA
            | Context::FACTORIAL
            | Context::LAMBERTW
            | Context::EI => Some(oo),
            Context::TANH | Context::ERF | Context::ZETA => Some(value(Rational::ONE)),
            Context::CI => Some(value(Rational::ZERO)),
            Context::ATAN | Context::SI => {
                Some(Term::Symbol(SymbolTerm::new(Context::PI, self)) / value(Rational::from(2)))
            }
            _ => None,
        }
    }

    /// Evaluate `sin`, `cos` or `tan` at `{$q pi$}` for the angles with values in radicals, `q` being a multiple of
    /// `{$1/12$}`, `{$1/10$}` or `{$1/8$}`, like `{$cos(pi/3) = 1/2$}`. `tan` stays unevaluated at its poles.
    fn eval_trig_at_pi_multiple(self, ident: Symbol, q: &Rational) -> Option<Term<Self>> {
        // `{$q pi = k pi / 120$}` with `{$0 <= k < 240$}`
        let parts = q * Rational::from(120);
        if parts.denominator_ref() != &Natural::ONE {
            return None;
        }
        let k = i64::try_from(&parts).ok()?.rem_euclid(240);
        let value = |n, d| Term::Value(Value::new(Rational::from_signeds(n, d), self));
        let sqrt = |x: Term<Self>| x.pow(&value(1, 2));
        let sqrt_of = |n| sqrt(value(n, 1));
        // `{$sin(k pi / 120)$}`
        let sin = |k: i64| -> Option<Term<Self>> {
            let (k, sign) = if k >= 120 { (k - 120, -1) } else { (k, 1) };
            let k = if k > 60 { 120 - k } else { k };
            let res = match k {
                0 => value(0, 1),
                10 => (sqrt_of(6) - sqrt_of(2)) / value(4, 1),
                12 => (sqrt_of(5) - value(1, 1)) / value(4, 1),
                15 => sqrt(value(2, 1) - sqrt_of(2)) / value(2, 1),
                20 => value(1, 2),
                24 => sqrt(value(10, 1) - value(2, 1) * sqrt_of(5)) / value(4, 1),
                30 => sqrt_of(2) / value(2, 1),
                36 => (sqrt_of(5) + value(1, 1)) / value(4, 1),
                40 => sqrt_of(3) / value(2, 1),
                45 => sqrt(value(2, 1) + sqrt_of(2)) / value(2, 1),
                48 => sqrt(value(10, 1) + value(2, 1) * sqrt_of(5)) / value(4, 1),
                50 => (sqrt_of(6) + sqrt_of(2)) / value(4, 1),
                60 => value(1, 1),
                _ => return None,
            };
            Some(value(sign, 1) * res)
        };
        let (sin_value, cos_value) = (sin(k), sin((k + 60) % 240));
        match ident {
            Context::SIN => sin_value,
            Context::COS => cos_value,
            _ => {
                let cos_value = cos_value?;
                (!cos_value.is_zero()).then(|| sin_value.map(|s| s / cos_value))?
            }
        }
    }

    /// `{$atan(tan theta) = theta - k pi$}` for a constant `{$theta$}`, `k` being the integer nearest to
    /// `{$theta / pi$}`, so `{$"arg"(e^(i theta))$}` is `{$theta$}` reduced into `{$(-pi, pi]$}`.
    fn eval_atan_of_tan(self, x: &Term<Self>) -> Option<Term<Self>> {
        let theta = match (x, expr::unary(x)) {
            (_, Some((Context::TAN, theta))) => theta.clone(),
            (Term::Mul(mul), _) => {
                let theta = mul.iter().find_map(|factor| match expr::unary(factor) {
                    Some((Context::SIN, theta)) => Some(theta.clone()),
                    _ => None,
                })?;
                if *x
                    != self.fun(Context::SIN, theta.clone()) / self.fun(Context::COS, theta.clone())
                {
                    return None;
                }
                theta
            }
            _ => return None,
        };
        let pi = Term::Symbol(SymbolTerm::new(Context::PI, self));
        // `{$theta/pi + 1/2$}` is never an integer since `{$cos theta != 0$}`, but must be far enough from one to
        // round with an approximation
        let shifted =
            approx::approximate_fixed(&(&theta / &pi), 64)? + Rational::from_signeds(1, 2);
        let k = Rational::from((&shifted).floor());
        let margin = Rational::from_signeds(1, 1_i64 << 32);
        if &shifted - &k < margin || &k + Rational::ONE - &shifted < margin {
            return None;
        }
        Some(theta - Term::Value(Value::new(k, self)) * pi)
    }

    /// Evaluate `asin`, `acos` or `atan` at the classic values, like `{$asin(1/2) = pi/6$}`.
    fn eval_inverse_trig(self, ident: Symbol, x: &Term<Self>) -> Option<Term<Self>> {
        let value = |n, d| Term::Value(Value::new(Rational::from_signeds(n, d), self));
        let sqrt = |n| value(n, 1).pow(&value(1, 2));
        let pi = Term::Symbol(SymbolTerm::new(Context::PI, self));
        let angle = |d| &pi / &value(d, 1);
        // Pairs `{$(x, f(x))$}` for non-negative `x`, `f` being odd
        let table = if ident == Context::ATAN {
            vec![
                (value(0, 1), value(0, 1)),
                (sqrt(3) / value(3, 1), angle(6)),
                (value(1, 1), angle(4)),
                (sqrt(3), angle(3)),
            ]
        } else {
            vec![
                (value(0, 1), value(0, 1)),
                (value(1, 2), angle(6)),
                (sqrt(2) / value(2, 1), angle(4)),
                (sqrt(3) / value(2, 1), angle(3)),
                (value(1, 1), angle(2)),
            ]
        };
        // Squares of the points: radicals have several forms, like `{$sqrt(3)/3 = sqrt(1/3)$}`
        let squares: &[(i64, i64)] = if ident == Context::ATAN {
            &[(0, 1), (1, 3), (1, 1), (3, 1)]
        } else {
            &[(0, 1), (1, 4), (1, 2), (3, 4), (1, 1)]
        };
        let opposite = -x;
        let square = x * x;
        let res = table
            .into_iter()
            .zip(squares)
            .find_map(|((at, res), &(n, d))| {
                if at == *x {
                    Some(res)
                } else if at == opposite {
                    Some(-res)
                } else if n != 0 && square == value(n, d) {
                    if Self::is_non_negative(x) {
                        Some(res)
                    } else if Self::is_non_negative(&opposite) {
                        Some(-res)
                    } else {
                        None
                    }
                } else {
                    None
                }
            })?;
        Some(if ident == Context::ACOS {
            // `{$acos(x) = pi/2 - asin(x)$}`
            angle(2) - res
        } else {
            res
        })
    }

    /// Evaluate `degree(f, x)`. Exponents of `x` may be symbolic when they are non-negative integers by the
    /// assumptions, the degree being their maximum, like `{$max(n, 10)$}` for `{$x^n + x^10$}`.
    fn eval_degree(self, fun: &dyn term::Function<Self>) -> Option<Term<Self>> {
        let (f, x) = degree_args(fun)?;
        let exponents = degree_exponents(f, x, |e| {
            sign::is_integer(e) && !sign::sign_set(e, SignMode::STRUCTURAL).contains(Ordering::Less)
        })?;
        // Drop the exponents smaller than another one
        let dominated = |e: &Term<Self>| {
            exponents.iter().any(|other| {
                other != e && {
                    let difference =
                        sign::sign_set(&(other.clone() - e.clone()), SignMode::STRUCTURAL);
                    !difference.contains(Ordering::Less)
                }
            })
        };
        let mut maxima: Vec<_> = exponents
            .iter()
            .filter(|e| !dominated(e))
            .cloned()
            .collect();
        if maxima.is_empty() {
            maxima = exponents;
        }
        // Values last, like `{$max(n, 10)$}`
        maxima.sort_by_key(|e| matches!(e, Term::Value(_)));
        Some(if maxima.len() == 1 {
            maxima.pop()?
        } else {
            Term::Fun(Box::new(Fun::new(Context::MAX, maxima, self))).normalize()
        })
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
        parser.is_literal_and(|value| Ok(Some(parse_rational_literal(value, "Integer")?)))
    }
}

impl Field for R<Rational> {}

impl Derivable for R<Rational> {
    fn derivative(&self, _: &Self::Element, _: Symbol) -> Self::Element {
        Rational::ZERO
    }

    fn derivative_function(&self, fun: &dyn term::Function<Self>, x: Symbol) -> Option<Term<Self>> {
        // A whole series, term by term
        if fun.get_ident() != Context::held_sum() {
            return None;
        }
        crate::sum::derive_held_sum(fun.get_args::<Self>()?, x)
    }
}

/// The real field, using [`malachite::rational::Rational`] as constants to get arbitrary precision numbers.
pub const R: R<Rational> = R {
    phantom: PhantomData,
};
