//! Substitution of a symbol by an expression.

use crate::{context::Symbol, field::Ring};

use super::{Fun, Mul, Normalize, Term};

impl<T: Ring> Term<T> {
    /// Replace `symbol` by `value` in the expression, normalizing the result.
    ///
    /// Returns `None` if `symbol` appears where it can't be replaced, like in an exponent or in the arguments of a
    /// function from another set.
    ///
    /// ```
    /// use formalith::{field::real::R, parse, symbol};
    ///
    /// let term = parse!("x^2 + y", R).substitute(symbol!("x"), &parse!("y + 1", R));
    /// assert_eq!(term, Some(parse!("(y + 1)^2 + y", R)));
    /// assert_eq!(parse!("2^x", R).substitute(symbol!("x"), &parse!("1", R)), None);
    /// ```
    #[must_use]
    pub fn substitute(&self, symbol: Symbol, value: &Self) -> Option<Self> {
        if !self.symbols().contains(&symbol) {
            return Some(self.clone());
        }
        let set = self.get_set();
        Some(match self {
            Self::Value(_) => unreachable!("A value has no symbol"),
            Self::Symbol(_) => value.clone(),
            Self::Add(add) => add.iter().try_fold(Self::zero(set), |res, term| {
                Some(res + term.substitute(symbol, value)?)
            })?,
            Self::Mul(mul) => {
                let factors = mul
                    .iter()
                    .map(|factor| factor.substitute(symbol, value))
                    .collect::<Option<_>>()?;
                Self::Mul(Mul::new(mul.coefficient.clone(), factors, set)).normalize()
            }
            Self::Pow(pow) => {
                if pow.exponant.symbols().contains(&symbol) {
                    return None;
                }
                pow.base.substitute(symbol, value)?.pow(&pow.exponant)
            }
            Self::Fun(fun) => {
                let args = fun
                    .get_args::<T>()?
                    .iter()
                    .map(|arg| arg.substitute(symbol, value))
                    .collect::<Option<_>>()?;
                Self::Fun(Box::new(Fun::new(fun.get_ident(), args, set))).normalize()
            }
        })
    }
}
