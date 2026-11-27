//! The sets `{$K^NN$}` of sequences, like `R^N`.

// Indices and orders are small
#![allow(clippy::cast_possible_wrap)]

pub mod numeric;
mod system;

use std::{cell::RefCell, cmp::Ordering, collections::BTreeSet};

pub use system::{Equation, MAX_SEQUENCE_STEPS, Sequence};
pub(crate) use system::{Ref, rewrite, substitute};

use crate::{
    context::{Context, Symbol},
    field::{
        Group, Monoid, PartiallyOrderedSet, Ring, Semiring, Set, SetParseExpression, matrix::M,
    },
    parser::{ParseExpression, Parser, lexer::TokenKind},
    printer::{PrettyPrint, PrettyPrinter, Print, PrintOptions},
    term::{Expand, Fun, Function, Normalize, SymbolTerm, Term, TermSet, relation::Relation},
};

/// The sets whose sequences can be computed: rings whose exponents and coefficients are themselves.
pub trait SequenceValues: Ring<ExponantSet = Self, ProductCoefficientSet = Self> {}

impl<K: Ring<ExponantSet = K, ProductCoefficientSet = K>> SequenceValues for K {}

/// The ring `{$K^NN$}` of the sequences of elements of `K`, indexed by a symbol (`n` by default).
///
/// The index is parsed as the sequence `{$(n)_n$}`, other expressions as their general term: `{$n^2 + 1$}` is the
/// sequence `{$(n^2 + 1)_n$}`, a constant is a constant sequence. Operations and functions are componentwise. A
/// sequence may also be given by a recurrence, `recurrence(u(n) = 2 u(n - 1) + 1, u(0) = 1)`, whose terms
/// `term(u, m)` are computed by iteration, and shifted by `shift(u, k)`.
/// ```
/// use formalith::{field::{Set, real::R}, parse, symbol};
///
/// let r_n = R.get_sequence_set(symbol!("n"));
/// assert_eq!(parse!("expand((n + 1)^2 - n^2)", r_n), parse!("2 n + 1", r_n));
/// assert_eq!(
///     parse!("term(recurrence(u(n) = 2 u(n - 1) + 1, u(0) = 1), 10)", r_n),
///     parse!("2047", r_n)
/// );
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Seq<K> {
    values: K,
    index: Symbol,
}

impl<K> Seq<K> {
    /// Create the set of the sequences of elements of `values`, indexed by `index`.
    pub const fn new(values: K, index: Symbol) -> Self {
        Self { values, index }
    }

    /// The set of the terms.
    pub const fn values(&self) -> &K {
        &self.values
    }

    /// The index.
    pub const fn index(&self) -> Symbol {
        self.index
    }
}

impl<K: SequenceValues> Seq<K> {
    /// The index as an expression of `K`.
    const fn index_term(&self) -> Term<K> {
        Term::Symbol(SymbolTerm::new(self.index, self.values))
    }

    /// The sequence as a value.
    const fn value(self, sequence: Sequence<K>) -> Term<Self> {
        Term::constant(sequence, self)
    }

    /// The integer `m` of a constant sequence `{$(m)_n$}`.
    fn integer(&self, a: &Sequence<K>) -> Option<i64> {
        match a.as_closed()? {
            Term::Value(value) => self.values.to_i64(&value.value),
            _ => None,
        }
    }

    /// Evaluate a builtin: `term`, `shift`, and the other functions componentwise. `None` when they can't be
    /// evaluated, like a term of a symbolic index or a limit in a recurrence.
    fn eval_builtin(self, fun: &dyn Function<Self>) -> Option<Term<Self>> {
        let args = fun.get_args::<Self>()?;
        let values = args
            .iter()
            .map(|arg| match arg {
                Term::Value(value) => Some(&value.value),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        match (fun.get_ident(), values.as_slice()) {
            (Context::TERM, [u, m]) => {
                let m = self.integer(m)?;
                Some(self.value(Sequence::closed(u.at(self, m)?)))
            }
            (Context::SHIFT, [u, k]) => Some(self.value(u.shift(self, self.integer(k)?))),
            (Context::TERM | Context::SHIFT | Context::RECURRENCE, _) => None,
            // Builtins binding a variable are only evaluated on closed forms, their references being sequences
            (
                Context::LIM
                | Context::SUM
                | Context::PRODUCT
                | Context::INTEGRATE
                | Context::DIFF
                | Context::SERIES
                | Context::SUBS
                | Context::SOLVE,
                _,
            ) if values.iter().any(|value| value.as_closed().is_none()) => None,
            (ident, _) => Some(self.value(Sequence::map(&values, self, |terms| {
                Term::Fun(Box::new(Fun::new(ident, terms, self.values))).normalize()
            }))),
        }
    }

    /// The sequence as an expression of `K`: its general term, or `recurrence(u(n) = ..., u(0) = ...)` with the
    /// equations of its system.
    fn as_term(self, a: &Sequence<K>) -> Term<K> {
        if let Some(rule) = a.as_closed() {
            return rule.clone();
        }
        let set = self.values;
        let mut used = BTreeSet::new();
        for equation in a.equations() {
            used.extend(equation.rule.symbols());
            for value in equation
                .initial
                .iter()
                .chain(equation.overrides.iter().map(|(_, v)| v))
            {
                used.extend(value.symbols());
            }
        }
        used.insert(self.index);
        let names: Vec<Symbol> = Symbol::fresh(&["u", "v", "w"], "u", |symbol| {
            used.contains(&symbol)
                || Context::builtin_arity(symbol).is_some()
                || symbol.name() == "i"
        })
        .take(a.equations().len())
        .collect();
        let call = |name: Symbol, arg: Term<K>| {
            Term::Fun(Box::new(Fun::new(name, vec![arg], set))).normalize()
        };
        let relation = |lhs, rhs| {
            Term::Fun(Box::new(Fun::new(
                Relation::Equal.symbol(),
                vec![lhs, rhs],
                set,
            )))
        };
        let mut relations = vec![];
        for (j, equation) in a.equations().iter().enumerate() {
            let rule = rewrite(&equation.rule, &mut |t| {
                let Term::Symbol(s) = t else { return None };
                let (i, d) = match Ref::parse(s.symbol)? {
                    Ref::Own(d) => (j, d),
                    Ref::Other(i, d) => (i, d),
                };
                let at = self.index_term() - Term::nth(d as i64, set);
                Some(call(names[i], at))
            });
            relations.push(relation(call(names[j], self.index_term()), rule));
            let start = equation.start;
            let given = equation
                .initial
                .iter()
                .enumerate()
                .map(|(i, value)| (start + i as i64, value))
                .chain(equation.overrides.iter().map(|(n, value)| (*n, value)));
            for (n, value) in given {
                relations.push(relation(call(names[j], Term::nth(n, set)), value.clone()));
            }
        }
        Term::Fun(Box::new(Fun::new(Context::RECURRENCE, relations, set)))
    }

    /// The sequence `recurrence(relations)`: the relations `u(n) = rule` define the equations, in order, the last
    /// one being the sequence, and the relations `u(m) = value` their initial values or the values replacing their
    /// rule.
    ///
    /// # Errors
    /// Returns a message when a name has no rule, an initial value is missing, or a rule refers to a sequence
    /// other than at `{$n - d$}`, `{$d >= 1$}` for its own sequence (`{$d >= 0$}` for an earlier one).
    pub(crate) fn recurrence(
        &self,
        relations: &[(Term<K>, Term<K>)],
    ) -> Result<Sequence<K>, String> {
        let set = self.values;
        let index = self.index_term();
        let mut names: Vec<Symbol> = vec![];
        let mut rules = vec![];
        let mut cases: Vec<Vec<(i64, Term<K>)>> = vec![];
        let head = |lhs: &Term<K>| -> Result<(Symbol, Option<i64>), String> {
            if let Term::Fun(fun) = lhs
                && let Some([arg]) = fun.get_args::<K>().map(Vec::as_slice)
            {
                if *arg == index {
                    return Ok((fun.get_ident(), None));
                }
                if let Term::Value(value) = arg
                    && let Some(m) = set.to_i64(&value.value)
                {
                    return Ok((fun.get_ident(), Some(m)));
                }
            }
            Err(format!(
                "expected `u({0}) = ...` or `u(0) = ...` in recurrence, found `{lhs} = ...`",
                self.index.name()
            ))
        };
        for (lhs, rhs) in relations {
            let (name, case) = head(lhs)?;
            let position = names.iter().position(|n| *n == name);
            match (case, position) {
                (None, Some(_)) => {
                    return Err(format!("`{}` has two rules", name.name()));
                }
                (None, None) => {
                    names.push(name);
                    rules.push(rhs.clone());
                    cases.push(vec![]);
                }
                (Some(m), Some(position)) => cases[position].push((m, rhs.clone())),
                (Some(m), None) => {
                    // A value given before the rule
                    names.push(name);
                    rules.push(Term::Symbol(SymbolTerm::new(Context::UNDEFINED, set)));
                    cases.push(vec![(m, rhs.clone())]);
                }
            }
        }
        let mut equations = vec![];
        for (j, name) in names.iter().enumerate() {
            if matches!(&rules[j], Term::Symbol(s) if s.symbol == Context::UNDEFINED) {
                return Err(format!(
                    "`{}` has no rule `{0}({}) = ...`",
                    name.name(),
                    self.index.name()
                ));
            }
            let error = RefCell::new(None);
            let rule = rewrite(&rules[j], &mut |t| {
                let Term::Fun(fun) = t else { return None };
                let i = names.iter().position(|n| *n == fun.get_ident())?;
                let delay = match fun.get_args::<K>().map(Vec::as_slice) {
                    Some([arg]) => match (index.clone() - arg.clone()).normalize() {
                        Term::Value(value) => set.to_i64(&value.value),
                        _ => None,
                    },
                    _ => None,
                };
                let r = match delay.and_then(|d| usize::try_from(d).ok()) {
                    Some(d) if i == j && d >= 1 => Some(Ref::Own(d)),
                    Some(d) if i < j => Some(Ref::Other(i, d)),
                    _ => None,
                };
                if r.is_none() {
                    *error.borrow_mut() = Some(format!(
                        "the rule of `{}` can only refer to `{}` at `{} - d` with d >= {}, found `{t}`",
                        name.name(),
                        fun.get_ident().name(),
                        self.index.name(),
                        u8::from(i == j),
                    ));
                }
                Some(r.map_or_else(|| Term::zero(set), |r| r.term(set)))
            });
            if let Some(error) = error.into_inner() {
                return Err(error);
            }
            let given = std::mem::take(&mut cases[j]);
            equations.push(with_cases(Equation::closed(rule), given, *name).map_err(|e| e.0)?);
        }
        if equations.is_empty() {
            return Err("recurrence expects relations `u(n) = ...`".to_owned());
        }
        Ok(Sequence::from_equations(equations, *self))
    }

    /// Parse `recurrence(u(n) = rule, u(0) = value, ...)`, its relations being expressions of `K` without the
    /// definitions of the parser.
    fn parse_recurrence(
        &self,
        parser: &mut Parser,
    ) -> Result<Option<Term<Self>>, crate::parser::ParserError>
    where
        K: SetParseExpression,
        K::ProductCoefficientSet: SetParseExpression,
    {
        let TokenKind::Ident(name) = &parser.token.kind else {
            return Ok(None);
        };
        if *name != Context::RECURRENCE.name() {
            return Ok(None);
        }
        let mut next = parser.clone();
        next.next_token();
        if next.token.kind != TokenKind::OpenParen {
            return Ok(None);
        }
        next.next_token();
        *parser = next;
        let env = parser.take_environment();
        let mut relations = vec![];
        let res = (|| {
            loop {
                let side = |parser: &mut Parser| {
                    ParseExpression::<K>::parse_expression(parser, 0, self.values)?
                        .map(|term| term.normalize())
                        .ok_or_else(|| {
                            parser.error_here(format!(
                                "expected a relation `u({}) = ...`, found {}",
                                self.index.name(),
                                parser.describe_token()
                            ))
                        })
                };
                let lhs = side(parser)?;
                parser.expect_token(&TokenKind::Equal)?;
                let rhs = side(parser)?;
                relations.push((lhs, rhs));
                if parser.token.kind != TokenKind::Comma {
                    break;
                }
                parser.next_token();
            }
            parser.expect_token(&TokenKind::CloseParen)
        })();
        parser.restore_environment(env);
        res?;
        let sequence = self
            .recurrence(&relations)
            .map_err(crate::parser::ParserError::new)?;
        Ok(Some(self.value(sequence)))
    }
}

/// A missing initial value of a recurrence, see [`with_cases`].
#[derive(Debug)]
pub(crate) struct MissingInitialValue(pub String);

/// The equation of a sequence `name` with the values `given` at integers: the first ones are the initial values of a
/// recurrence, as many as its order, the others replace its rule.
///
/// # Errors
/// Returns a message when an initial value is missing.
pub(crate) fn with_cases<K: SequenceValues>(
    mut equation: Equation<K>,
    mut given: Vec<(i64, Term<K>)>,
    name: Symbol,
) -> Result<Equation<K>, MissingInitialValue> {
    let order = equation.order();
    given.sort_by_key(|(n, _)| *n);
    given.dedup_by_key(|(n, _)| *n);
    if order > 0 {
        let start = given.first().map_or(0, |(n, _)| *n);
        equation.start = start;
        for n in start..start + order as i64 {
            let Some(position) = given.iter().position(|(m, _)| *m == n) else {
                return Err(MissingInitialValue(format!(
                    "`{}` needs the initial value {0}({n})",
                    name.name()
                )));
            };
            equation.initial.push(given.remove(position).1);
        }
    }
    equation.overrides = given;
    Ok(equation)
}

impl<K: SequenceValues> Seq<K> {
    /// The recurrence whose rule is `body`, a sequence whose last rule refers to the sequence itself at `{$n - d$}`
    /// through the symbols `placeholder(d)`, with the values `given` at integers, see [`with_cases`].
    ///
    /// # Errors
    /// Returns a message when an initial value is missing, or when the sequence itself is used elsewhere than in the
    /// last rule.
    pub(crate) fn close_recursive(
        &self,
        body: &Sequence<K>,
        placeholder: impl Fn(Symbol) -> Option<usize>,
        given: Vec<(i64, Term<K>)>,
        name: Symbol,
    ) -> Result<Sequence<K>, (bool, String)> {
        let mut equations = body.equations.to_vec();
        let last = equations.len() - 1;
        for (j, equation) in equations.iter_mut().enumerate() {
            let has_placeholder = equation
                .rule
                .symbols()
                .into_iter()
                .any(|s| placeholder(s).is_some());
            if !has_placeholder {
                continue;
            }
            if j != last || equation.order() > 0 {
                return Err((
                    false,
                    format!("`{}` can't be used there in its own rule", name.name()),
                ));
            }
            equation.rule = rewrite(&equation.rule, &mut |t| match t {
                Term::Symbol(s) => placeholder(s.symbol).map(|d| Ref::Own(d).term(self.values)),
                _ => None,
            });
        }
        let equation = equations.pop().expect("A system has an equation");
        let equation = with_cases(equation, given, name).map_err(|e| (true, e.0))?;
        equations.push(equation);
        Ok(Sequence::from_equations(equations, *self))
    }

    /// The sequence `a` of this set, indexed by `index` in `a`.
    pub(crate) fn reindexed(&self, a: &Sequence<K>, index: Symbol) -> Sequence<K> {
        if index == self.index {
            return a.clone();
        }
        let to = self.index_term();
        let rename = |term: &Term<K>| substitute(term, index, &to);
        let equations: Vec<Equation<K>> = a
            .equations
            .iter()
            .map(|equation| Equation {
                start: equation.start,
                initial: equation.initial.iter().map(rename).collect(),
                overrides: equation
                    .overrides
                    .iter()
                    .map(|(n, value)| (*n, rename(value)))
                    .collect(),
                rule: rename(&equation.rule),
            })
            .collect();
        Sequence::from_equations(equations, *self)
    }

    /// The sequence as a value of this set.
    pub(crate) const fn sequence_value(self, sequence: Sequence<K>) -> Term<Self> {
        Term::constant(sequence, self)
    }

    /// The integer of a constant sequence.
    pub(crate) fn as_integer(&self, a: &Sequence<K>) -> Option<i64> {
        self.integer(a)
    }

    /// The index as an expression of the terms.
    pub(crate) const fn index_as_term(&self) -> Term<K> {
        self.index_term()
    }
}

impl<K: SequenceValues> Set for Seq<K> {
    type Element = Sequence<K>;
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
        Print::print(&self.as_term(elem), options, f)
    }
    fn pretty_print(&self, elem: &Self::Element, options: &PrintOptions) -> PrettyPrinter {
        PrettyPrint::pretty_print(&self.as_term(elem), options)
    }
    fn element_eq(&self, a: &Self::Element, b: &Self::Element) -> bool {
        a == b
            || self
                .sub(a, b)
                .as_closed()
                .is_some_and(|d| d.is_zero() || d.expand().is_zero())
    }
    fn is_atomic(&self, elem: &Self::Element) -> bool {
        match elem.as_closed() {
            Some(Term::Value(value)) => self.values.is_atomic(&value.value),
            Some(Term::Symbol(_) | Term::Fun(_)) | None => true,
            Some(_) => false,
        }
    }
    fn is_sum(&self, elem: &Self::Element) -> bool {
        match elem.as_closed() {
            Some(Term::Value(value)) => self.values.is_sum(&value.value),
            Some(Term::Add(_)) => true,
            _ => false,
        }
    }
}

impl<K: SequenceValues> PartiallyOrderedSet for Seq<K> {
    /// Sequences are only compared when they are constants.
    fn partial_cmp(&self, a: &Self::Element, b: &Self::Element) -> Option<Ordering> {
        if a == b {
            return Some(Ordering::Equal);
        }
        match (a.as_closed()?, b.as_closed()?) {
            (Term::Value(a), Term::Value(b)) => self.values.partial_cmp(&a.value, &b.value),
            _ => None,
        }
    }
}

impl<K: SequenceValues> Monoid for Seq<K> {
    fn zero(&self) -> Self::Element {
        Sequence::closed(Term::zero(self.values))
    }

    fn is_zero(&self, a: &Self::Element) -> bool {
        a.as_closed().is_some_and(Term::is_zero)
    }

    fn add(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        Sequence::map(&[a, b], *self, |terms| &terms[0] + &terms[1])
    }

    fn to_i64(&self, a: &Self::Element) -> Option<i64> {
        self.integer(a)
    }
}

impl<K: SequenceValues> Group for Seq<K> {
    fn nth(&self, nth: i64) -> Self::Element {
        Sequence::closed(Term::nth(nth, self.values))
    }

    fn neg(&self, a: &Self::Element) -> Self::Element {
        Sequence::map(&[a], *self, |terms| -&terms[0])
    }

    fn sub(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        Sequence::map(&[a, b], *self, |terms| &terms[0] - &terms[1])
    }
}

impl<K: SequenceValues> Semiring for Seq<K> {
    fn one(&self) -> Self::Element {
        Sequence::closed(Term::one(self.values))
    }

    fn is_one(&self, a: &Self::Element) -> bool {
        a.as_closed().is_some_and(Term::is_one)
    }

    fn mul(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        Sequence::map(&[a, b], *self, |terms| &terms[0] * &terms[1])
    }

    /// Fold the expression into a single sequence: symbols are constant sequences, and sums, products, powers and
    /// functions of sequences are computed componentwise.
    fn normalize(&self, a: Term<Self>) -> Term<Self> {
        let value = |term: &Term<Self>| match term {
            Term::Value(value) => Some(value.value.clone()),
            _ => None,
        };
        match &a {
            Term::Symbol(symbol) if symbol.symbol != Context::UNDEFINED => self.value(
                Sequence::closed(Term::Symbol(SymbolTerm::new(symbol.symbol, self.values))),
            ),
            Term::Add(add) => add
                .iter()
                .map(value)
                .collect::<Option<Vec<_>>>()
                .map_or(a.clone(), |terms| {
                    self.value(terms.iter().fold(self.zero(), |res, t| self.add(&res, t)))
                }),
            Term::Mul(mul) => {
                mul.iter()
                    .map(value)
                    .collect::<Option<Vec<_>>>()
                    .map_or(a.clone(), |factors| {
                        self.value(
                            factors
                                .iter()
                                .fold(mul.coefficient.clone(), |res, t| self.mul(&res, t)),
                        )
                    })
            }
            Term::Pow(pow) => match (value(&pow.base), value(&pow.exponant)) {
                (Some(base), Some(exponant)) => {
                    self.value(Sequence::map(&[&base, &exponant], *self, |terms| {
                        terms[0].pow(&terms[1])
                    }))
                }
                _ => a,
            },
            Term::Fun(fun) => self.eval_builtin(&**fun).unwrap_or(a),
            _ => a,
        }
    }
    fn expand(&self, a: Term<Self>) -> Term<Self> {
        match &a {
            Term::Value(value) => self.value(value.value.map_rules(*self, Expand::expand)),
            _ => a,
        }
    }

    fn simplify(&self, a: Term<Self>) -> Term<Self> {
        match &a {
            Term::Value(value) => self.value(value.value.map_rules(*self, Term::simplify)),
            _ => a,
        }
    }
}

impl<K: SequenceValues> Ring for Seq<K> {
    /// The componentwise inverse, except for zero.
    fn try_inv(&self, a: &Self::Element) -> Option<Self::Element> {
        if self.is_zero(a) {
            return None;
        }
        Some(Sequence::map(&[a], *self, |terms| terms[0].inv()))
    }
}

impl<K: SequenceValues + SetParseExpression> SetParseExpression for Seq<K>
where
    K::ProductCoefficientSet: SetParseExpression,
{
    type MatrixArgumentSet = M<TermSet<Self>>;

    fn get_matrix_argument_set(&self) -> Self::MatrixArgumentSet {
        self.get_term_set().get_matrix_set()
    }

    fn parse_literal(&self, parser: &mut Parser) -> Result<Option<Self::Element>, String> {
        if matches!(&parser.token.kind, TokenKind::Ident(ident) if *ident == self.index.name()) {
            parser.next_token();
            return Ok(Some(Sequence::closed(self.index_term())));
        }
        Ok(self
            .values
            .parse_literal(parser)?
            .map(|c| Sequence::closed(Term::constant(c, self.values))))
    }

    fn is_constant(&self, name: &str) -> bool {
        name == self.index.name() || self.values.is_constant(name)
    }

    fn is_index(&self, name: &str) -> bool {
        name == self.index.name()
    }

    fn parse_expression(
        &self,
        parser: &mut Parser,
    ) -> Result<Option<Term<Self>>, crate::parser::ParserError> {
        self.parse_recurrence(parser)
    }
}
