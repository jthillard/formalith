//! Symbolic differentiation of expressions.

use crate::{
    context::{Context, Symbol},
    field::Derivable,
};

use super::{Flags, Fun, Normalize, SymbolTerm, Term, Value};

impl<T: Derivable<ExponantSet = T, ProductCoefficientSet = T>> Term<T> {
    /// Derivative of the expression with respect to `x`.
    ///
    /// Parts which can't be differentiated, like `floor` or unknown functions, are kept as an unevaluated
    /// `diff(f, x)`.
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
                let exponant = &**pow.exponant;
                let exponant_derivative = exponant.derivative(x);
                if !exponant_derivative.is_zero() {
                    // `{$(b^e)' = b^e (e' ln b + e b' / b)$}`
                    let ln = Self::Fun(Box::new(Fun::new(
                        Context::LN,
                        vec![(*pow.base).clone()],
                        set,
                    )))
                    .normalize();
                    return self
                        * &(exponant_derivative * ln
                            + exponant * &pow.base.derivative(x) / &*pow.base);
                }
                // `{$(b^e)' = e b^(e-1) b'$}`
                exponant * &pow.base.pow(&(exponant - &Self::one(set))) * pow.base.derivative(x)
            }
            Self::Fun(fun) => {
                // `{$d/dx integral f dif x = f$}`
                if fun.get_ident() == Context::INTEGRATE
                    && let Some([f, Self::Symbol(variable)]) =
                        fun.get_args::<T>().map(Vec::as_slice)
                    && variable.symbol == x
                {
                    return f.clone();
                }
                // `{$d/dx integral_a^b f(t) dif t = f(b) b' - f(a) a'$}`
                if fun.get_ident() == Context::INTEGRATE
                    && let Some([f, Self::Symbol(t), a, b]) = fun.get_args::<T>().map(Vec::as_slice)
                    && t.symbol != x
                    && !f.symbols().contains(&x)
                    && let (Some(at_a), Some(at_b)) =
                        (f.substitute(t.symbol, a), f.substitute(t.symbol, b))
                {
                    return at_b * b.derivative(x) - at_a * a.derivative(x);
                }
                // Values of `piecewise` are differentiated, except at the boundaries of the conditions
                if fun.get_ident() == Context::PIECEWISE
                    && let Some(args) = fun.get_args::<T>()
                {
                    let conditions = args.len() / 2;
                    let args = args
                        .iter()
                        .enumerate()
                        .map(|(i, arg)| {
                            if i % 2 == 0 && i / 2 < conditions {
                                arg.clone()
                            } else {
                                arg.derivative(x)
                            }
                        })
                        .collect();
                    return Self::Fun(Box::new(Fun::new(Context::PIECEWISE, args, set)))
                        .normalize();
                }
                // `{$d/dx psi^((m))(u) = psi^((m + 1))(u) u'$}`
                if fun.get_ident() == Context::POLYGAMMA
                    && let Some([m, u]) = fun.get_args::<T>().map(Vec::as_slice)
                    && !m.symbols().contains(&x)
                {
                    let order = m.clone() + Self::one(set);
                    let outer = Self::Fun(Box::new(Fun::new(
                        Context::POLYGAMMA,
                        vec![order, u.clone()],
                        set,
                    )))
                    .normalize();
                    return outer * u.derivative(x);
                }
                if let Some([u]) = fun.get_args::<T>().map(Vec::as_slice) {
                    // `{$psi(v)$}`
                    let digamma = |v: Self| {
                        Self::Fun(Box::new(Fun::new(
                            Context::POLYGAMMA,
                            vec![Self::zero(set), v],
                            set,
                        )))
                        .normalize()
                    };
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
                        // `{$"erf"' = 2/sqrt(pi) e^(-u^2)$}`, `{$"erfi"' = 2/sqrt(pi) e^(u^2)$}`
                        Context::ERF | Context::ERFI => {
                            let square = if fun.get_ident() == Context::ERF {
                                -(u * u)
                            } else {
                                u * u
                            };
                            let pi = Self::Symbol(SymbolTerm::new(Context::PI, set));
                            Some(
                                (&one + &one)
                                    * inv_sqrt(pi)
                                    * Self::Fun(Box::new(Fun::new(
                                        Context::EXP,
                                        vec![square],
                                        set,
                                    )))
                                    .normalize(),
                            )
                        }
                        // `{$Gamma'(u) = Gamma(u) psi(u)$}`, `{$(u!)' = u! psi(u + 1)$}`
                        Context::GAMMA => Some(self * &digamma(u.clone())),
                        Context::FACTORIAL => Some(self * &digamma(u.clone() + one.clone())),
                        // `{$W'(u) = W(u) / (u (1 + W(u)))$}`
                        Context::LAMBERTW => Some(self / &(u * &(&one + self))),
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
