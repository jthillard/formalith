//! Definitions of sequences: definitions with values at integers, like `u(0) := 1` and `u(n) := 2 u(n - 1) + 1`,
//! referring to themselves.
//!
//! Such a definition is built as a sequence of `{$K^NN$}` ([`Seq`]): its rule is parsed in `{$K^NN$}` with its
//! parameter as the index, its own calls `u(n - d)` standing for the recurrence. In a set of sequences, the
//! definition is the whole sequence `u`, `u(n + k)` a shift and `u(m)` a term. In `R` and `C`, `u(m)` is the term
//! for an integer `m`, computed by iteration, `u(x)` staying unevaluated for a symbol `x`; in `Z`, terms are
//! computed in `R`. Elsewhere, calls stay unevaluated.
//!
//! A definition may have other parameters, the index being the parameter at the position of the integers of its
//! values: `f(c, 0) := c` and `f(c, n) := f(c, n - 1)^2 + c` is a sequence of parameter `c`, its own calls being
//! `f(c, n - d)`. A call `f(1/2, 3)` binds `c` to `1/2` before building the sequence, and the whole sequence `f`
//! keeps the symbol `c`.

use std::{cell::RefCell, rc::Rc};

use malachite::{Integer, Rational};

use crate::{
    context::{Context, Symbol},
    field::{
        Set, SetParseExpression,
        complex::C,
        integer::Z,
        real::R,
        sequence::{Seq, Sequence, SequenceValues},
    },
    printer::{Print, PrintOptions},
    term::{Fun, Normalize, SymbolTerm, Term, relation::Relation},
};

use super::{
    Parser, ParserError,
    environment::{Definition, Environment},
};

thread_local! {
    /// The sequences whose rule is being parsed, innermost last.
    static BUILDING: RefCell<Vec<*const Definition>> = const { RefCell::new(vec![]) };
}

/// Pops [`BUILDING`] when dropped.
struct Building;

impl Building {
    fn enter(definition: &Rc<Definition>) -> Self {
        BUILDING.with(|building| building.borrow_mut().push(Rc::as_ptr(definition)));
        Self
    }
}

impl Drop for Building {
    fn drop(&mut self) {
        BUILDING.with(|building| building.borrow_mut().pop());
    }
}

/// Where `definition` is in [`BUILDING`]: `Some(true)` for the innermost one.
fn building(definition: &Rc<Definition>) -> Option<bool> {
    BUILDING.with(|building| {
        let building = building.borrow();
        let position = building.iter().position(|d| *d == Rc::as_ptr(definition))?;
        Some(position + 1 == building.len())
    })
}

/// The symbol standing for the sequence itself at `{$n - d$}` while its rule is parsed.
fn placeholder(d: usize) -> Symbol {
    Symbol::new(format!("@b{d}"))
}

/// The shift `d` of a symbol of [`placeholder`].
fn placeholder_delay(symbol: Symbol) -> Option<usize> {
    symbol.name().strip_prefix("@b")?.parse().ok()
}

/// An error building a sequence, `missing` when an initial value is missing (the values may be given later).
struct BuildError {
    missing: bool,
    error: ParserError,
}

impl From<ParserError> for BuildError {
    fn from(error: ParserError) -> Self {
        Self {
            missing: false,
            error,
        }
    }
}

/// The parameters of `definition` other than its index.
fn other_params(definition: &Definition) -> Vec<Symbol> {
    let mut params = definition.params().to_vec();
    if definition.index() < params.len() {
        params.remove(definition.index());
    }
    params
}

/// The sequence of `definition`, in the set of sequences of `values` indexed by its index, its other parameters
/// being symbols, or bound to the sources of `bound`.
fn build<K>(
    definition: &Rc<Definition>,
    values: K,
    bound: Option<Vec<String>>,
) -> Result<(Seq<K>, Sequence<K>), BuildError>
where
    K: SequenceValues + SetParseExpression,
{
    let Some(&param) = definition.params().get(definition.index()) else {
        return Err(ParserError::new(format!(
            "`{}` has no index to have values at integers",
            definition.name().name()
        ))
        .into());
    };
    let set = Seq::new(values, param);
    let others = other_params(definition);
    let mut env: Environment = definition.env().without(param);
    for other in &others {
        env = env.without(*other);
    }
    if let Some(bound) = bound {
        env.bind(&others, bound, &Environment::new());
    }
    let mut given = vec![];
    for case in definition.cases() {
        // The names of the parameters in this value stand for those of the rule
        let mut case_env = env.clone();
        let names = others.iter().map(|p| p.name().to_owned()).collect();
        case_env.bind(case.params(), names, &env);
        let value = Parser::new(case.source())
            .with_offset(None)
            .with_environment(&case_env)
            .parse(values)?;
        given.push((case.m(), value));
    }
    env.insert_rc(Rc::clone(definition));
    let body = if let Some(body) = definition.body() {
        let _building = Building::enter(definition);
        match Parser::new(body)
            .with_offset(None)
            .with_environment(&env)
            .parse(set)?
        {
            Term::Value(value) => value.value,
            _ => {
                return Err(ParserError::new(format!(
                    "the rule of `{}` isn't a sequence",
                    definition.name().name()
                ))
                .into());
            }
        }
    } else {
        // Only values are given, the rule stays unevaluated
        let mut args: Vec<Term<K>> = others
            .iter()
            .map(|p| Term::Symbol(SymbolTerm::new(*p, values)))
            .collect();
        args.insert(definition.index().min(args.len()), set.index_as_term());
        Sequence::closed(call(definition.name(), args, values))
    };
    let sequence = set
        .close_recursive(&body, placeholder_delay, given, definition.name())
        .map_err(|(missing, error)| BuildError {
            missing,
            error: ParserError::new(error),
        })?;
    Ok((set, sequence))
}

/// The call `name(args)`, unevaluated.
fn call<E: Set>(name: Symbol, args: Vec<Term<E>>, set: E) -> Term<E> {
    Term::Fun(Box::new(Fun::new(name, args, set))).normalize()
}

/// Expansions of the definitions of sequences in a set.
pub trait ExpandSequence: Set {
    /// The call `name(args)` of the sequence `definition`, `args` being sources parsed by `parser`.
    fn expand_sequence(
        parser: &Parser,
        definition: &Rc<Definition>,
        args: &[String],
        set: Self,
    ) -> Result<Term<Self>, ParserError>;

    /// The whole sequence `definition`, in a set of sequences.
    fn whole_sequence(
        definition: &Rc<Definition>,
        set: Self,
    ) -> Result<Option<Term<Self>>, ParserError>;
}

/// The arguments of `args` parsed in `set`.
fn parse_args<E: Set>(
    parser: &Parser,
    args: &[String],
    set: E,
) -> Result<Vec<Term<E>>, ParserError> {
    args.iter()
        .map(|arg| parser.parse_source(arg, set))
        .collect()
}

impl<E: Set> ExpandSequence for E {
    /// The call stays unevaluated.
    default fn expand_sequence(
        parser: &Parser,
        definition: &Rc<Definition>,
        args: &[String],
        set: Self,
    ) -> Result<Term<Self>, ParserError> {
        let args = parse_args(parser, args, set)?;
        Ok(Term::Fun(Box::new(Fun::new(definition.name(), args, set))).normalize())
    }

    default fn whole_sequence(
        _: &Rc<Definition>,
        _: Self,
    ) -> Result<Option<Term<Self>>, ParserError> {
        Ok(None)
    }
}

/// The sets whose terms of sequences are computed, `R` and `C`.
trait Terms: SequenceValues + SetParseExpression {}

impl Terms for R<Rational> {}
impl Terms for C<R<Rational>> {}

/// Check that a sequence is called with as many arguments as it has parameters, returning the index argument
/// and the others.
fn split_args<'a>(
    definition: &Definition,
    args: &'a [String],
) -> Result<(&'a String, Vec<&'a String>), ParserError> {
    let arity = definition.params().len();
    if args.len() != arity {
        let plural = if arity == 1 { "" } else { "s" };
        return Err(ParserError::new(format!(
            "`{}` expects {arity} argument{plural}, found {}",
            definition.name().name(),
            args.len()
        )));
    }
    let index = definition.index().min(arity - 1);
    let others = args
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != index)
        .map(|(_, arg)| arg)
        .collect();
    Ok((&args[index], others))
}

/// The sources binding the parameters other than the index to `others`, `None` if one of them refers to `index`,
/// which would stand for the index in the rule.
fn bindings<K: Set>(others: &[Term<K>], index: Symbol) -> Option<Vec<String>> {
    others
        .iter()
        .map(|arg| {
            (!arg.symbols().contains(&index))
                .then(|| arg.with_options(PrintOptions::plain()).to_string())
        })
        .collect()
}

/// The term of `definition` at `arg` in `K`, the other parameters being `others`: computed for an integer,
/// written with the rule of a definition which isn't recursive (a `piecewise` of its values), unevaluated
/// otherwise.
fn scalar_term<K: Terms>(
    definition: &Rc<Definition>,
    arg: &Term<K>,
    others: &[Term<K>],
) -> Result<Term<K>, ParserError> {
    let values = arg.get_set();
    let unevaluated = || {
        let mut args = others.to_vec();
        args.insert(definition.index().min(args.len()), arg.clone());
        call(definition.name(), args, values)
    };
    let m = match arg {
        Term::Value(value) => values.to_i64(&value.value),
        _ => None,
    };
    if m.is_none() && definition.is_recursive() {
        return Ok(unevaluated());
    }
    let index = definition.params()[definition.index()];
    let Some(bound) = bindings(others, index) else {
        return Ok(unevaluated());
    };
    let (set, sequence) = match build(definition, values, Some(bound)) {
        Ok(built) => built,
        Err(BuildError { missing: true, .. }) => return Ok(unevaluated()),
        Err(BuildError { error, .. }) => return Err(error),
    };
    if let Some(m) = m {
        return Ok(sequence.at(set, m).unwrap_or_else(unevaluated));
    }
    // A closed form with values at some integers
    let [equation] = sequence.equations() else {
        return Ok(unevaluated());
    };
    let general = crate::field::sequence::substitute(&equation.rule, set.index(), arg);
    if equation.overrides.is_empty() {
        return Ok(general);
    }
    let mut pieces = vec![];
    for (n, value) in &equation.overrides {
        pieces.push(Term::Fun(Box::new(Fun::new(
            Relation::Equal.symbol(),
            vec![arg.clone(), Term::nth(*n, values)],
            values,
        ))));
        pieces.push(value.clone());
    }
    pieces.push(general);
    Ok(Term::Fun(Box::new(Fun::new(Context::PIECEWISE, pieces, values))).normalize())
}

impl<K: Terms> ExpandSequence for K {
    fn expand_sequence(
        parser: &Parser,
        definition: &Rc<Definition>,
        args: &[String],
        set: Self,
    ) -> Result<Term<Self>, ParserError> {
        let (arg, others) = split_args(definition, args)?;
        let arg = parser.parse_source(arg, set)?;
        let others: Vec<_> = others
            .into_iter()
            .map(|other| parser.parse_source(other, set))
            .collect::<Result<_, _>>()?;
        scalar_term(definition, &arg, &others)
    }
}

impl ExpandSequence for Z<Integer> {
    /// Terms are computed in `R`, the rationals containing the integers.
    fn expand_sequence(
        parser: &Parser,
        definition: &Rc<Definition>,
        args: &[String],
        set: Self,
    ) -> Result<Term<Self>, ParserError> {
        let (arg, others) = split_args(definition, args)?;
        let others: Vec<_> = others
            .into_iter()
            .map(|other| parser.parse_source(other, R))
            .collect::<Result<_, _>>()?;
        let term = scalar_term(definition, &parser.parse_source(arg, R)?, &others)?;
        if let Term::Value(_) = term {
            let source = term.with_options(PrintOptions::plain()).to_string();
            return parser.parse_source(&source, set);
        }
        let args = parse_args(parser, args, set)?;
        Ok(Term::Fun(Box::new(Fun::new(definition.name(), args, set))).normalize())
    }
}

impl<K: SequenceValues + SetParseExpression> ExpandSequence for Seq<K> {
    fn expand_sequence(
        parser: &Parser,
        definition: &Rc<Definition>,
        args: &[String],
        set: Self,
    ) -> Result<Term<Self>, ParserError> {
        let name = definition.name().name();
        match building(definition) {
            // The sequence itself at `{$n - d$}`, in its own rule
            Some(true) => {
                let (arg, others) = split_args(definition, args)?;
                let params = other_params(definition);
                let own_head = || {
                    let mut args: Vec<String> =
                        params.iter().map(|p| p.name().to_owned()).collect();
                    args.insert(
                        definition.index().min(args.len()),
                        format!("{} - d", set.index().name()),
                    );
                    format!("{name}({})", args.join(", "))
                };
                // The other parameters are passed as they are
                if others
                    .iter()
                    .zip(&params)
                    .any(|(other, param)| other.trim() != param.name())
                {
                    return Err(ParserError::new(format!(
                        "the rule of `{name}` can only refer to `{}` with d >= 1, found `{name}({})`",
                        own_head(),
                        args.join(", ")
                    )));
                }
                let arg = parser.parse_source(arg, set)?;
                let delay = match &arg {
                    Term::Value(value) => value.value.as_closed().and_then(|rule| {
                        match (set.index_as_term() - rule.clone()).normalize() {
                            Term::Value(d) => set.values().to_i64(&d.value),
                            _ => None,
                        }
                    }),
                    _ => None,
                };
                return match delay.and_then(|d| usize::try_from(d).ok()) {
                    Some(d) if d >= 1 => Ok(set.sequence_value(Sequence::closed(Term::Symbol(
                        SymbolTerm::new(placeholder(d), *set.values()),
                    )))),
                    _ => Err(ParserError::new(format!(
                        "the rule of `{name}` can only refer to `{}` with d >= 1, found `{name}({})`",
                        own_head(),
                        args.join(", ")
                    ))),
                };
            }
            Some(false) => {
                return Err(ParserError::new(format!(
                    "`{name}` is used in the rule of another sequence of its own rule, mutually recursive \
                     sequences aren't supported"
                )));
            }
            None => {}
        }
        if args.is_empty() {
            let (built_set, sequence) =
                build(definition, *set.values(), None).map_err(|error| error.error)?;
            return Ok(set.sequence_value(set.reindexed(&sequence, built_set.index())));
        }
        let (arg, others) = split_args(definition, args)?;
        let arg = parser.parse_source(arg, set)?;
        let others: Vec<_> = others
            .into_iter()
            .map(|other| parser.parse_source(other, set))
            .collect::<Result<_, _>>()?;
        let unevaluated = || {
            let mut args = others.clone();
            args.insert(definition.index().min(args.len()), arg.clone());
            call(definition.name(), args, set)
        };
        // The other parameters are constant sequences, not referring to the index of the definition
        let index = definition.params()[definition.index()];
        let constants: Option<Vec<Term<K>>> = others
            .iter()
            .map(|other| match other {
                Term::Value(value) => value
                    .value
                    .as_closed()
                    .filter(|rule| !rule.symbols().contains(&set.index()))
                    .cloned(),
                _ => None,
            })
            .collect();
        let Some(bound) = constants.and_then(|constants| bindings(&constants, index)) else {
            return Ok(unevaluated());
        };
        let (built_set, sequence) =
            build(definition, *set.values(), Some(bound)).map_err(|error| error.error)?;
        let sequence = set.reindexed(&sequence, built_set.index());
        let Term::Value(value) = &arg else {
            return Ok(unevaluated());
        };
        let Some(rule) = value.value.as_closed() else {
            return Ok(unevaluated());
        };
        // `u(n + k)`
        if let Term::Value(k) = (rule.clone() - set.index_as_term()).normalize()
            && let Some(k) = set.values().to_i64(&k.value)
        {
            return Ok(set.sequence_value(sequence.shift(set, k)));
        }
        // `u(m)`
        if let Some(m) = set.as_integer(&value.value)
            && let Some(term) = sequence.at(set, m)
        {
            return Ok(set.sequence_value(Sequence::closed(term)));
        }
        Ok(unevaluated())
    }

    fn whole_sequence(
        definition: &Rc<Definition>,
        set: Self,
    ) -> Result<Option<Term<Self>>, ParserError> {
        match build(definition, *set.values(), None) {
            Ok((built_set, sequence)) => Ok(Some(
                set.sequence_value(set.reindexed(&sequence, built_set.index())),
            )),
            Err(BuildError { missing: true, .. }) => Ok(None),
            Err(BuildError { error, .. }) => Err(error),
        }
    }
}

/// The whole sequence `definition` in `set` if it is a set of sequences, for the result of its definition.
///
/// # Errors
/// Returns an error when the rule of the sequence is invalid.
pub fn whole<E: Set>(definition: &Rc<Definition>, set: E) -> Result<Option<Term<E>>, ParserError> {
    E::whole_sequence(definition, set)
}
