//! Symbolic differentiation of expressions.

use crate::{
    context::{Context, Symbol},
    field::Derivable,
};

use super::{Flags, Fun, Normalize, SymbolTerm, Term, Value};

impl<T: Derivable<ExponantSet = T, ProductCoefficientSet = T>> Term<T> {
    /// Derivative of the expression with respect to `x`.
    ///
    /// Parts which can't be differentiated, like functions other than `exp`, `ln`, `sin`, `cos` and `tan`, or `{$x^x$}`,
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
                if let Some([u]) = fun.get_args::<T>().map(Vec::as_slice) {
                    let apply = |ident| {
                        Self::Fun(Box::new(Fun::new(ident, vec![u.clone()], set))).normalize()
                    };
                    // `{$f(u)' = f'(u) u'$}`
                    let outer = match fun.get_ident() {
                        Context::EXP => Some(self.clone()),
                        Context::LN => Some(u.inv()),
                        Context::SIN => Some(apply(Context::COS)),
                        Context::COS => Some(-apply(Context::SIN)),
                        // `{$tan' = 1 + tan^2$}`
                        Context::TAN => Some(Self::one(set) + self * self),
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
