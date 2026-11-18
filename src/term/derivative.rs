//! Symbolic differentiation of expressions.

use crate::{
    context::{Context, Symbol},
    field::Derivable,
};

use super::{Flags, Fun, Normalize, SymbolTerm, Term, Value};

impl<T: Derivable<ExponantSet = T, ProductCoefficientSet = T>> Term<T> {
    /// Derivative of the expression with respect to `x`.
    ///
    /// Parts which can't be differentiated, like `abs` or `{$x^x$}`,
    /// are kept as an unevaluated `diff(f, x)`.
    #[must_use]
    pub fn derivative(&self, x: Symbol) -> Self {
        let set = self.get_set();
        match self {
            Self::Value(value) => Self::constant(set.derivative(&value.value, x), set),
            Self::Symbol(symbol) => {
                if symbol.symbol == x {
                    Self::one(set)
                } else {
                    Self::zero(set)
                }
            }
            Self::Add(add) => add
                .iter()
                .fold(Self::zero(set), |res, term| res + term.derivative(x)),
            Self::Mul(mul) => {
                let coefficient = Self::Value(Value::new(mul.coefficient.clone(), set));
                // `{$(c f_1 ... f_n)' = c' f_1 ... f_n + c sum_i f_i' product_(j != i) f_j$}`
                let mut res = mul.iter().fold(coefficient.derivative(x), |res, f| res * f);
                for (i, factor) in mul.iter().enumerate() {
                    res += mul
                        .iter()
                        .enumerate()
                        .filter(|(j, _)| *j != i)
                        .fold(&coefficient * &factor.derivative(x), |res, (_, f)| res * f);
                }
                res
            }
            Self::Pow(pow) => {
                if !pow.exponant.derivative(x).is_zero() {
                    return self.unevaluated_derivative(x);
                }
                // `{$(b^e)' = e b^(e-1) b'$}`
                let exponant = &**pow.exponant;
                exponant * &pow.base.pow(&(exponant - &Self::one(set))) * pow.base.derivative(x)
            }
            Self::Fun(fun) => {
                // `{$d/dx integral f dif x = f$}`
                if fun.get_ident() == Context::INTEGRATE
                    && let Some([f, Self::Symbol(variable)]) = fun.get_args::<T>().map(Vec::as_slice)
                    && variable.symbol == x
                {
                    return f.clone();
                }
                if let Some([u]) = fun.get_args::<T>().map(Vec::as_slice) {
                    let apply = |ident| {
                        Self::Fun(Box::new(Fun::new(ident, vec![u.clone()], set))).normalize()
                    };
                    let one = Self::one(set);
                    // `{$1 / sqrt(v)$}`
                    let inv_sqrt = |v: Self| v.pow(&-(&one + &one).inv());
                    // `{$f(u)' = f'(u) u'$}`
                    let outer = match fun.get_ident() {
                        Context::EXP => Some(self.clone()),
                        Context::LN => Some(u.inv()),
                        Context::SIN => Some(apply(Context::COS)),
                        Context::COS => Some(-apply(Context::SIN)),
                        // `{$tan' = 1 + tan^2$}`
                        Context::TAN => Some(one.clone() + self * self),
                        Context::SINH => Some(apply(Context::COSH)),
                        Context::COSH => Some(apply(Context::SINH)),
                        // `{$tanh' = 1 - tanh^2$}`
                        Context::TANH => Some(one.clone() - self * self),
                        // `{$asin' = 1 / sqrt(1 - u^2)$}`, `{$acos' = -1 / sqrt(1 - u^2)$}`
                        Context::ASIN => Some(inv_sqrt(&one - &(u * u))),
                        Context::ACOS => Some(-inv_sqrt(&one - &(u * u))),
                        Context::ATAN => Some((&one + &(u * u)).inv()),
                        Context::ASINH => Some(inv_sqrt(u * u + one.clone())),
                        Context::ACOSH => Some(inv_sqrt(u * u - one.clone())),
                        Context::ATANH => Some((&one - &(u * u)).inv()),
                        // `{$|u|' = sign(u) u'$}`, except at 0
                        Context::ABS => Some(apply(Context::SIGN)),
                        // `{$sign' = 0$}`, except at 0
                        Context::SIGN => Some(Self::zero(set)),
                        _ => None,
                    };
                    if let Some(outer) = outer {
                        return outer * u.derivative(x);
                    }
                }
                self.unevaluated_derivative(x)
            }
        }
    }

    /// Build `diff(self, x)` without normalizing it, which would try to differentiate again.
    fn unevaluated_derivative(&self, x: Symbol) -> Self {
        let set = self.get_set();
        let args = vec![self.clone(), Self::Symbol(SymbolTerm::new(x, set))];
        let mut res = Self::Fun(Box::new(Fun::new(Context::DIFF, args, set)));
        res.set_normalized(true);
        res
    }
}
