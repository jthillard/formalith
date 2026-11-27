//! Definitions of sequences: definitions of one variable with values at integers, like `u(0) := 1` and
//! `u(n) := 2 u(n - 1) + 1`, referring to themselves.
//!
//! Such a definition is built as a sequence of `{$K^NN$}` ([`Seq`]): its rule is parsed in `{$K^NN$}` with its
//! parameter as the index, its own calls `u(n - d)` standing for the recurrence. In a set of sequences, the
//! definition is the whole sequence `u`, `u(n + k)` a shift and `u(m)` a term. In `R` and `C`, `u(m)` is the term
//! for an integer `m`, computed by iteration, `u(x)` staying unevaluated for a symbol `x`; in `Z`, terms are
//! computed in `R`. Elsewhere, calls stay unevaluated.

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

/// The sequence of `definition`, in the set of sequences of `values` indexed by its parameter.
fn build<K>(definition: &Rc<Definition>, values: K) -> Result<(Seq<K>, Sequence<K>), BuildError>
where
    K: SequenceValues + SetParseExpression,
{
    let [param] = definition.params() else {
        return Err(ParserError::new(format!(
            "`{}` must have a single parameter to have values at integers",
            definition.name().name()
        ))
        .into());
    };
    let set = Seq::new(values, *param);
    let mut env: Environment = definition.env().without(*param);
    let mut given = vec![];
    for (m, source) in definition.cases() {
        let value = Parser::new(source)
            .with_offset(None)
            .with_environment(&env)
            .parse(values)?;
        given.push((*m, value));
    }
    env.insert_rc(Rc::clone(definition));
    let body = match definition.body() {
        Some(body) => {
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
        }
        // Only values are given, the rule stays unevaluated
        None => Sequence::closed(call(definition.name(), set.index_as_term())),
    };
    let sequence = set
        .close_recursive(&body, placeholder_delay, given, definition.name())
        .map_err(|(missing, error)| BuildError {
            missing,
            error: ParserError::new(error),
        })?;
    Ok((set, sequence))
}

/// The call `name(arg)`, unevaluated.
fn call<E: Set>(name: Symbol, arg: Term<E>) -> Term<E> {
    let set = arg.get_set();
    Term::Fun(Box::new(Fun::new(name, vec![arg], set))).normalize()
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

/// The single argument of a sequence.
fn single<'a>(definition: &Definition, args: &'a [String]) -> Result<&'a String, ParserError> {
    match args {
        [arg] => Ok(arg),
        _ => Err(ParserError::new(format!(
            "`{}` expects 1 argument, found {}",
            definition.name().name(),
            args.len()
        ))),
    }
}

/// The term of `definition` at `arg` in `K`: computed for an integer, written with the rule of a definition
/// which isn't recursive (a `piecewise` of its values), unevaluated otherwise.
fn scalar_term<K: Terms>(
    definition: &Rc<Definition>,
    arg: &Term<K>,
) -> Result<Term<K>, ParserError> {
    let values = arg.get_set();
    let unevaluated = || call(definition.name(), arg.clone());
    let m = match arg {
        Term::Value(value) => values.to_i64(&value.value),
        _ => None,
    };
    if m.is_none() && definition.is_recursive() {
        return Ok(unevaluated());
    }
    let (set, sequence) = match build(definition, values) {
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
        let arg = parser.parse_source(single(definition, args)?, set)?;
        scalar_term(definition, &arg)
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
        let arg = single(definition, args)?;
        let term = scalar_term(definition, &parser.parse_source(arg, R)?)?;
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
                let arg = parser.parse_source(single(definition, args)?, set)?;
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
                        "the rule of `{name}` can only refer to `{name}` at `{0} - d` with d >= 1, found \
                         `{name}({arg})`",
                        set.index().name(),
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
        let (built_set, sequence) =
            build(definition, *set.values()).map_err(|error| error.error)?;
        let sequence = set.reindexed(&sequence, built_set.index());
        let arg = match args {
            [] => return Ok(set.sequence_value(sequence)),
            [arg] => parser.parse_source(arg, set)?,
            _ => {
                single(definition, args)?;
                unreachable!("More than one argument is an error")
            }
        };
        let Term::Value(value) = &arg else {
            return Ok(call(definition.name(), arg));
        };
        let Some(rule) = value.value.as_closed() else {
            return Ok(call(definition.name(), arg));
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
        Ok(call(definition.name(), arg))
    }

    fn whole_sequence(
        definition: &Rc<Definition>,
        set: Self,
    ) -> Result<Option<Term<Self>>, ParserError> {
        match build(definition, *set.values()) {
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
