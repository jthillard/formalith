//! Parser implementation, used in [`crate::parse`] and [`crate::try_parse`] macros.

pub mod environment;
pub mod lexer;

use std::error::Error;
use std::fmt::{Debug, Display};
use std::iter::Peekable;
use std::ops::Range;

use malachite::{Integer, Natural};

use crate::context::{Context, Symbol};
use crate::field::{
    Group, Monoid, Ring, Semiring, Set, SetParseExpression, integer::Z, natural::N,
};
use crate::printer::{Print, PrintOptions};
use crate::term::{Fun, Mul, Normalize, SymbolTerm, Term, Value, flags::Flags, relation::Relation};

use environment::Environment;
use lexer::{Lexer, LiteralTokenKind, Token, TokenKind};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Op {
    Add,
    Subtract,
    Multiply,
    Divide,
    Pow,
}
impl Op {
    pub const fn get_priority(self) -> usize {
        match self {
            Self::Pow => 14,
            Self::Multiply | Self::Divide => 13,
            Self::Add | Self::Subtract => 12,
        }
    }
}

/// Represent an error raised by the parser
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParserError {
    message: String,
}

impl ParserError {
    /// Create a new parser error.
    #[must_use]
    pub fn new<T: Into<String>>(message: T) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl From<ParserError> for String {
    fn from(value: ParserError) -> Self {
        value.message
    }
}

impl Error for ParserError {}

impl Display for ParserError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

/// A parser over a string input.
#[derive(Debug, Clone)]
pub struct Parser<'a> {
    input: &'a str,
    lexer: Peekable<Lexer<'a>>,
    prev_token: Token,
    /// The current token
    pub token: Token,
    start_span: usize,
    end_span: usize,
    env: Option<&'a Environment>,
    /// The unknown function and its variable while parsing a differential equation, see [`Parser::parse_ode_function`]
    ode: Option<(Symbol, Symbol)>,
    /// The priority of the expression being parsed, so that literals parsing a whole expression (the scalars of
    /// `M<TermSet<R>>`) stop at the same operators, `{$A^2 + 2 A$}` not being `{$A^(2 + 2 A)$}`
    pub(crate) priority: usize,
    /// Whether a scalar of a matrix set is being parsed, so that builtins returning matrices aren't parsed as
    /// scalars (see [`Context::returns_matrix`]), except inside parentheses
    pub(crate) scalar_of_matrix: bool,
}

impl<'a> Parser<'a> {
    /// Create a new parser over the `input` string.
    #[must_use]
    pub fn new(input: &'a str) -> Self {
        let mut parser = Parser {
            input,
            lexer: Lexer::new(input).peekable(),
            prev_token: Token::new(TokenKind::Unknown, 0),
            token: Token::new(TokenKind::Unknown, 0),
            start_span: 0,
            end_span: 0,
            env: None,
            ode: None,
            scalar_of_matrix: false,
            priority: 0,
        };
        parser.next_token();
        parser
    }

    /// Expand the definitions of `env` while parsing.
    #[must_use]
    pub const fn with_environment(mut self, env: &'a Environment) -> Self {
        self.env = Some(env);
        self
    }
}

/// Parse an expression living in the set `E`. Implemented for every set, but parsing fails at runtime
/// for sets that don't implement [`SetParseExpression`].
pub trait ParseExpression<E: Set> {
    /// Parse an expression, which can be a literal, a sum, a group in parenthesis () ...
    ///
    /// # Errors
    /// This method can return an error if the parsing failed.
    fn parse_expression(&mut self, priority: usize, set: E)
    -> Result<Option<Term<E>>, ParserError>;
}

impl Parser<'_> {
    /// Return the next lexer token and advance current span
    fn next_token_internal(&mut self) -> Option<Token> {
        let next = self.lexer.next();
        self.start_span = self.end_span;
        if let Some(span) = &next {
            self.end_span += span.len;
        }
        next
    }
    /// Update the current and previous token, skipping unnecessary tokens
    pub fn next_token(&mut self) {
        let next = loop {
            match self.next_token_internal() {
                None => break Token::new(TokenKind::Eof, 0),
                Some(Token {
                    kind: TokenKind::Whitespace,
                    ..
                }) => {}
                Some(token) => break token,
            }
        };
        self.prev_token = std::mem::replace(&mut self.token, next);
    }
    const fn span(&self) -> Range<usize> {
        self.start_span..self.end_span
    }
    /// Eat a token with a specific kind, raising an error if the current token kind doesn't match.
    ///
    /// # Errors
    /// The method returns a `ParserError` if the kind of the current token is not the one expected.
    pub fn expect_token(&mut self, kind: &TokenKind) -> Result<(), ParserError> {
        match &self.token.kind {
            k if k == kind => {
                self.next_token();
                Ok(())
            }
            _ => Err(ParserError::new(format!(
                "expect {:?}, found {:?}",
                kind, self.token.kind
            ))),
        }
    }
    /// Whether the current token starts an implicit product with the operand just before it: an identifier or a
    /// parenthesis after a number, an identifier, a closing parenthesis or bracket, a factorial or a prime, with or
    /// without spaces (`2x`, `x y`, `(x + 1)y`, `5 (x + 1)`). An identifier followed by a parenthesis is a call
    /// (`f (x)`), parsed before, and a number is never an implicit factor (`x 2` is an error, `xy` an identifier).
    /// A builtin function name isn't a factor either, so `sin x` is an error rather than `sin*x`.
    fn implicit_product(&self) -> bool {
        let ends_operand = match &self.prev_token.kind {
            TokenKind::Ident(name) => !matches!(
                Context::builtin_arity(Symbol::new(name.as_str())),
                Some((min, _)) if min > 0
            ),
            kind => matches!(
                kind,
                TokenKind::Literal {
                    kind: LiteralTokenKind::Int | LiteralTokenKind::Float,
                } | TokenKind::CloseParen
                    | TokenKind::CloseBracket
                    | TokenKind::Bang
                    | TokenKind::Prime
            ),
        };
        ends_operand && matches!(self.token.kind, TokenKind::OpenParen | TokenKind::Ident(_))
    }
    /// Return the next operator if it exists, juxtaposed operands being an implicit product (see
    /// [`Parser::implicit_product`])
    fn get_op(&self) -> Option<Op> {
        if self.implicit_product() {
            return Some(Op::Multiply);
        }
        match self.token.kind {
            TokenKind::Plus => Some(Op::Add),
            TokenKind::Minus => Some(Op::Subtract),
            TokenKind::Star => Some(Op::Multiply),
            TokenKind::Slash => Some(Op::Divide),
            TokenKind::Caret => Some(Op::Pow),
            _ => None,
        }
    }
    /// Parse the parser's string, returning the parsed mathematical expression.
    ///
    /// # Errors
    /// This method can return an error if the parsing failed.
    pub fn parse<E: Set>(&mut self, set: E) -> Result<Term<E>, ParserError> {
        let _assumptions = self.env.map(|env| env.assumptions().enter());
        let term = self.parse_operand(set)?.ok_or_else(|| {
            if self.token.kind == TokenKind::Eof {
                ParserError::new("Input was empty")
            } else {
                ParserError::new(format!("Unexpected token at position {}", self.start_span))
            }
        })?;
        self.expect_eof()?;
        Ok(term.normalize())
    }

    /// Parse an expression, without normalizing it, checking that no operator is left.
    fn parse_operand<E: Set>(&mut self, set: E) -> Result<Option<Term<E>>, ParserError> {
        let term = ParseExpression::<E>::parse_expression(self, 0, set)?;
        if let Some(op) = self.get_op() {
            return Err(ParserError::new(format!(
                "Operand expected for binary operation {op:?} at position {}",
                self.end_span
            )));
        }
        Ok(term)
    }

    /// Check that the whole input was parsed.
    fn expect_eof(&self) -> Result<(), ParserError> {
        if self.token.kind != TokenKind::Eof {
            return Err(ParserError::new(format!(
                "Unexpected {:?} at position {}",
                self.token.kind, self.start_span
            )));
        }
        Ok(())
    }

    fn parse_symbol<E: Set>(&mut self, set: E) -> Option<Term<E>> {
        match &self.token.kind {
            TokenKind::Ident(sym) => {
                let tmp = sym.clone();
                self.next_token();
                Some(Term::Symbol(SymbolTerm::new(Symbol::new(tmp), set)))
            }
            _ => None,
        }
    }
    fn parse_group<E: Set>(&mut self, set: E) -> Result<Option<Term<E>>, ParserError> {
        match &self.token.kind {
            TokenKind::OpenParen => {
                self.next_token();
                let scalar_of_matrix = std::mem::replace(&mut self.scalar_of_matrix, false);
                let content = ParseExpression::<E>::parse_expression(self, 0, set);
                self.scalar_of_matrix = scalar_of_matrix;
                let content = content?.ok_or_else(|| {
                    ParserError::new(format!(
                        "Expression expected at position {}",
                        self.start_span
                    ))
                })?;
                self.expect_token(&TokenKind::CloseParen)?;
                Ok(Some(content))
            }
            _ => Ok(None),
        }
    }

    /// Expand the definition of the current identifier, if any.
    fn parse_definition<E: Set>(&mut self, set: E) -> Result<Option<Term<E>>, ParserError> {
        let (TokenKind::Ident(name), Some(env)) = (&self.token.kind, self.env) else {
            return Ok(None);
        };
        let Some(definition) = env.get(Symbol::new(name.as_str())) else {
            return Ok(None);
        };
        self.next_token();
        let name = definition.name().name();
        let params = definition.params();
        let args = if self.token.kind == TokenKind::OpenParen {
            if params.is_empty() {
                return Err(ParserError::new(format!("`{name}` is not a function")));
            }
            self.next_token();
            self.parse_args_source()?
        } else {
            vec![]
        };
        if args.len() != params.len() {
            let plural = if params.len() == 1 { "" } else { "s" };
            return Err(ParserError::new(format!(
                "Function {name} expects {} argument{plural}, found {}",
                params.len(),
                args.len()
            )));
        }
        let mut body_env = definition.env().clone();
        body_env.bind(params, args, env);
        let mut parser = Parser::new(definition.body()).with_environment(&body_env);
        let term = ParseExpression::<E>::parse_expression(&mut parser, 0, set)?;
        if parser.token.kind != TokenKind::Eof {
            return Err(ParserError::new(format!(
                "Unexpected {:?} in the definition of {name}",
                parser.token.kind
            )));
        }
        Ok(term)
    }

    /// In a differential equation for `y(x)`, parse `y`, `y(x)` or `y''` (`k` primes), as the `k`-th derivative of
    /// `y(x)`, kept unevaluated.
    fn parse_ode_function<E: Set>(&mut self, set: E) -> Result<Option<Term<E>>, ParserError> {
        let (Some((function, x)), TokenKind::Ident(name)) = (self.ode, &self.token.kind) else {
            return Ok(None);
        };
        if Symbol::new(name.as_str()) != function {
            return Ok(None);
        }
        self.next_token();
        let mut order = 0;
        while self.token.kind == TokenKind::Prime {
            order += 1;
            self.next_token();
        }
        let x = Term::Symbol(SymbolTerm::new(x, set));
        if self.token.kind == TokenKind::OpenParen {
            self.next_token();
            let args = self.parse_args(set)?;
            self.expect_token(&TokenKind::CloseParen)?;
            if args.len() != 1 || args[0].normalize() != x {
                return Err(ParserError::new(format!(
                    "`{}` must be evaluated at `{}` in the equation",
                    function.name(),
                    x
                )));
            }
        }
        let mut res = Term::Fun(Box::new(Fun::new(function, vec![x.clone()], set))).normalize();
        for _ in 0..order {
            res = Term::Fun(Box::new(Fun::new(Context::DIFF, vec![res, x.clone()], set)));
            res.set_normalized(true);
        }
        Ok(Some(res))
    }

    /// Parse the input as a differential equation for `function(x)`, see [`Parser::parse_ode_function`].
    #[must_use]
    pub(crate) const fn with_ode(mut self, function: Symbol, x: Symbol) -> Self {
        self.ode = Some((function, x));
        self
    }

    /// Return the source of arguments of a function, up to the closing parenthesis.
    fn parse_args_source(&mut self) -> Result<Vec<String>, ParserError> {
        let mut args = vec![];
        let mut start = self.start_span;
        let mut depth = 0usize;
        loop {
            match self.token.kind {
                TokenKind::OpenParen | TokenKind::OpenBracket | TokenKind::OpenBrace => depth += 1,
                TokenKind::Comma | TokenKind::CloseParen if depth == 0 => {
                    let arg = self.input[start..self.start_span].trim();
                    if arg.is_empty() {
                        return Err(ParserError::new(format!(
                            "Argument expected at position {}",
                            self.start_span
                        )));
                    }
                    args.push(arg.to_owned());
                    let close = self.token.kind == TokenKind::CloseParen;
                    self.next_token();
                    if close {
                        return Ok(args);
                    }
                    start = self.start_span;
                    continue;
                }
                TokenKind::CloseParen | TokenKind::CloseBracket | TokenKind::CloseBrace => {
                    depth -= 1;
                }
                TokenKind::Eof => return Err(ParserError::new("expect CloseParen, found Eof")),
                _ => {}
            }
            self.next_token();
        }
    }

    /// Parse the arguments of `piecewise(c_1, v_1, ..., default)`, whose conditions are comparisons like `x < 0`,
    /// written `@lt(x, 0)` (see [`Relation`]).
    fn parse_piecewise_args<E: Set>(&mut self, set: E) -> Result<Vec<Term<E>>, ParserError> {
        let mut args = vec![];
        loop {
            let position = self.start_span;
            let lhs = ParseExpression::<E>::parse_expression(self, 0, set)?.ok_or_else(|| {
                ParserError::new(format!("Argument expected at position {position}"))
            })?;
            let arg = match Relation::from_token(&self.token.kind) {
                Some(relation) if args.len() % 2 == 0 => {
                    self.next_token();
                    let position = self.start_span;
                    let rhs =
                        ParseExpression::<E>::parse_expression(self, 0, set)?.ok_or_else(|| {
                            ParserError::new(format!("Expression expected at position {position}"))
                        })?;
                    Term::Fun(Box::new(Fun::new(relation.symbol(), vec![lhs, rhs], set)))
                }
                _ => lhs,
            };
            args.push(arg);
            if self.token.kind != TokenKind::Comma {
                break;
            }
            self.next_token();
        }
        let is_condition = |arg: &Term<E>| matches!(arg, Term::Fun(fun) if Relation::from_symbol(fun.get_ident()).is_some());
        let conditions = args.len() / 2;
        for (i, arg) in args.iter().enumerate() {
            if (i % 2 == 0 && i / 2 < conditions) != is_condition(arg) {
                return Err(ParserError::new(
                    "piecewise expects conditions like `x < 0` followed by values, and a default value",
                ));
            }
        }
        Ok(args)
    }

    /// parse arguments of a function, separated by a comma.
    fn parse_args<E: Set>(&mut self, arg_set: E) -> Result<Vec<Term<E>>, ParserError> {
        let scalar_of_matrix = std::mem::replace(&mut self.scalar_of_matrix, false);
        let args = self.parse_args_unscoped(arg_set);
        self.scalar_of_matrix = scalar_of_matrix;
        args
    }
    fn parse_args_unscoped<E: Set>(&mut self, arg_set: E) -> Result<Vec<Term<E>>, ParserError> {
        let mut args = vec![];
        loop {
            args.push(
                ParseExpression::<E>::parse_expression(self, 0, arg_set)?.ok_or_else(|| {
                    ParserError::new(format!("Argument expected at position {}", self.start_span))
                })?,
            );
            if self.token.kind != TokenKind::Comma {
                return Ok(args);
            }
            self.next_token();
        }
    }
}

impl<E: Set> ParseExpression<E> for Parser<'_> {
    default fn parse_expression(&mut self, _: usize, _: E) -> Result<Option<Term<E>>, ParserError> {
        Err(ParserError::new("Expressions can't be parsed in this set"))
    }
}

impl<E: SetParseExpression> ParseExpression<E> for Parser<'_>
where
    E::ProductCoefficientSet: SetParseExpression,
{
    fn parse_expression(
        &mut self,
        priority: usize,
        set: E,
    ) -> Result<Option<Term<E>>, ParserError> {
        if self.scalar_of_matrix
            && let TokenKind::Ident(name) = &self.token.kind
            && Context::returns_matrix(Symbol::new(name.as_str()))
        {
            // Not a scalar, the matrix set parses it, see `M::parse_literal`
            return Ok(None);
        }
        self.priority = priority;
        let mut self_in_coefficient_set = self.clone();
        let node = self.parse_ode_function(set)?;
        // Definitions are expanded in the outermost set, before sets parse identifiers (like scalars of `M`)
        let node = node.map_or_else(|| self.parse_definition(set), |n| Ok(Some(n)))?;
        let node = node.map_or_else(|| set.parse_expression(self), |n| Ok(Some(n)))?;
        let node = node.map_or_else(|| ParseUnary::<E>::parse_unary(self, set), |n| Ok(Some(n)))?;
        let node_in_coefficient_set =
            self_in_coefficient_set.parse_literal(set.get_coefficient_set());
        let node = node.map_or_else(
            || {
                // Nested expressions parsed above changed it
                self.priority = priority;
                self.parse_literal_term(set)
            },
            |n| Ok(Some(n)),
        )?;
        let node = node.or_else(|| self.parse_symbol(set));
        let node = node.map_or_else(|| self.parse_group(set), |n| Ok(Some(n)))?;
        // The literal of the coefficient set is the same node only if it spans the same tokens: for `{$-2 x + 7$}`
        // in `M`, the scalar is `{$-2 x + 7$}` but the node `{$-2$}`, an operand of `{$-2 x + 7$}`
        let node_in_coefficient_set = match node_in_coefficient_set {
            Ok(Some(_)) if self_in_coefficient_set.start_span != self.start_span => Ok(None),
            other => other,
        };

        match (node, node_in_coefficient_set) {
            (None, Err(_) | Ok(None)) => Ok(None),
            (Some(mut node), mut node_in_coefficient_set) => {
                // A parenthesized symbol isn't a function name, `{$(x)(y) = x y$}`
                if let (TokenKind::OpenParen, Term::Symbol(symbol)) = (&self.token.kind, &node)
                    && self.prev_token.kind != TokenKind::CloseParen
                {
                    self.next_token();
                    let ident = symbol.symbol;
                    let (fun, args_count): (Term<E>, _) = match ident {
                        Context::DET
                        | Context::TRANSPOSE
                        | Context::TRACE
                        | Context::RANK
                        | Context::KERNEL
                        | Context::CHARPOLY
                        | Context::EIGENVALUES
                        | Context::EIGENVECTORS
                        | Context::HERMITE
                        | Context::SMITH => {
                            let args = self.parse_args(set.get_matrix_argument_set())?;
                            let count = args.len();
                            (Term::Fun(Box::new(Fun::new(ident, args, set))), count)
                        }
                        // Matrix sizes are integers, whatever the set
                        Context::IDENTITY | Context::ZEROS => {
                            let args = self.parse_args(Z)?;
                            let count = args.len();
                            (Term::Fun(Box::new(Fun::new(ident, args, set))), count)
                        }
                        Context::PIECEWISE => {
                            let args = self.parse_piecewise_args(set)?;
                            let count = args.len();
                            (Term::Fun(Box::new(Fun::new(ident, args, set))), count)
                        }
                        _ => {
                            let args = self.parse_args(set)?;
                            let count = args.len();
                            (Term::Fun(Box::new(Fun::new(ident, args, set))), count)
                        }
                    };
                    self.expect_token(&TokenKind::CloseParen)?;
                    if let Some((min, max)) = Context::builtin_arity(ident)
                        && !(min..=max).contains(&args_count)
                    {
                        let plural = if max == 1 { "" } else { "s" };
                        let expected = match (min, max) {
                            (min, usize::MAX) => format!("at least {min} argument{plural}"),
                            (min, max) if min == max => format!("{min} argument{plural}"),
                            (min, max) => format!("{min} to {max} arguments"),
                        };
                        return Err(ParserError::new(format!(
                            "Function {} expects {expected}, found {args_count}",
                            ident.name()
                        )));
                    }
                    node = fun.normalize();
                }
                // Postfix factorials bind tighter than any operator: `{$n!^2 = (n!)^2$}`, `{$2^3! = 2^(3!)$}`
                while self.token.kind == TokenKind::Bang {
                    self.next_token();
                    node = Term::Fun(Box::new(Fun::new(Context::FACTORIAL, vec![node], set)))
                        .normalize();
                    node_in_coefficient_set = Err(ParserError::new("factorial of a coefficient"));
                }
                let mut op = self.get_op();
                while self.token.kind != TokenKind::Eof
                    && op.is_some()
                    && priority < op.as_ref().unwrap().get_priority()
                {
                    let before_op = self.clone();
                    if !self.implicit_product() {
                        self.next_token();
                    }
                    let (new_node, parsed) = ParseBinary::<E>::parse_binary_expr(
                        self,
                        node,
                        node_in_coefficient_set.clone(),
                        op.unwrap(),
                        set,
                    )?;
                    if node_in_coefficient_set.is_ok() {
                        node_in_coefficient_set =
                            Err(ParserError::new("node_in_coefficient_set is already used"));
                    }
                    node = new_node;
                    if !parsed {
                        // No operand in this set, let the caller handle the operator (like `2*[[1]]`, where `2` is parsed as a scalar)
                        *self = before_op;
                        break;
                    }
                    op = self.get_op();
                }
                Ok(Some(node))
            }
            (None, Ok(Some(_))) => Err(ParserError::new(format!(
                "Unexpected literal at position {}",
                self.start_span
            ))),
        }
    }
}
trait ParseBinary<E: Set> {
    fn parse_binary_expr(
        &mut self,
        current: Term<E>,
        current_in_coefficient_set: Result<
            Option<<<E as Set>::ProductCoefficientSet as Set>::Element>,
            ParserError,
        >,
        op: Op,
        set: E,
    ) -> Result<(Term<E>, bool), ParserError>;
}

impl<E: Set> ParseBinary<E> for Parser<'_> {
    default fn parse_binary_expr(
        &mut self,
        current: Term<E>,
        _current_in_coefficient_set: Result<
            Option<<<E as Set>::ProductCoefficientSet as Set>::Element>,
            ParserError,
        >,
        _op: Op,
        _set: E,
    ) -> Result<(Term<E>, bool), ParserError> {
        Ok((current, false))
    }
}

/// Rejects exponents that mean nothing in a set, like `x^(1/2)` in `Z/n` or `R[x]`, whose exponents are integers.
trait CheckExponent<E: Set> {
    fn check_exponent(exponent: &Term<E::ExponantSet>) -> Result<(), ParserError>;
}

impl<E: Set> CheckExponent<E> for Parser<'_> {
    default fn check_exponent(_: &Term<E::ExponantSet>) -> Result<(), ParserError> {
        Ok(())
    }
}

impl<E: Semiring<ExponantSet = Z<Integer>>> CheckExponent<E> for Parser<'_> {
    default fn check_exponent(exponent: &Term<Z<Integer>>) -> Result<(), ParserError> {
        check_integer_exponent(exponent)
    }
}

fn check_integer_exponent(exponent: &Term<Z<Integer>>) -> Result<(), ParserError> {
    if exponent.normalize().as_fraction(false).1.is_one() {
        Ok(())
    } else {
        Err(ParserError::new(format!(
            "the exponent {} isn't an integer",
            exponent.with_options(PrintOptions::plain())
        )))
    }
}

// In `N`, there is no division, so exponents must not be negative either
impl CheckExponent<N<Natural>> for Parser<'_> {
    fn check_exponent(exponent: &Term<Z<Integer>>) -> Result<(), ParserError> {
        check_integer_exponent(exponent)?;
        if exponent.normalize().is_strictly_negative() {
            return Err(ParserError::new(format!(
                "the exponent {} is negative, but division isn't defined in this set",
                exponent.with_options(PrintOptions::plain())
            )));
        }
        Ok(())
    }
}

// In `Z`, exponents are elements of the set itself, where `1/2` is a term like any other
impl CheckExponent<Z<Integer>> for Parser<'_> {
    fn check_exponent(_: &Term<Z<Integer>>) -> Result<(), ParserError> {
        Ok(())
    }
}

/// Applies a binary operator other than `^` to parsed operands, `-` and `/` being only defined in rings.
trait ApplyBinary<E: Set> {
    fn apply_binary(
        current: Term<E>,
        current_in_coefficient_set: Result<
            Option<<<E as Set>::ProductCoefficientSet as Set>::Element>,
            ParserError,
        >,
        op: Op,
        right: Term<E>,
        set: E,
    ) -> Result<Term<E>, ParserError>;
}

/// `+` and `*`, defined in every semiring.
fn apply_semiring_binary<E: Semiring>(
    current: Term<E>,
    current_in_coefficient_set: Result<
        Option<<<E as Set>::ProductCoefficientSet as Set>::Element>,
        ParserError,
    >,
    op: Op,
    right: Term<E>,
    set: E,
) -> Result<Term<E>, ParserError> {
    match op {
        Op::Add => Ok(current + right),
        Op::Multiply => Ok(if let Ok(Some(current)) = current_in_coefficient_set {
            Term::Mul(Mul::new(current, vec![right], set)).normalize()
        } else {
            current * right
        }),
        Op::Subtract => Err(ParserError::new(
            "subtraction isn't defined in this set, which has no additive inverses",
        )),
        Op::Divide => Err(ParserError::new("division isn't defined in this set")),
        Op::Pow => unreachable!(),
    }
}

impl<E: Semiring> ApplyBinary<E> for Parser<'_> {
    default fn apply_binary(
        current: Term<E>,
        current_in_coefficient_set: Result<
            Option<<<E as Set>::ProductCoefficientSet as Set>::Element>,
            ParserError,
        >,
        op: Op,
        right: Term<E>,
        set: E,
    ) -> Result<Term<E>, ParserError> {
        apply_semiring_binary(current, current_in_coefficient_set, op, right, set)
    }
}

impl<E: Ring> ApplyBinary<E> for Parser<'_> {
    fn apply_binary(
        current: Term<E>,
        current_in_coefficient_set: Result<
            Option<<<E as Set>::ProductCoefficientSet as Set>::Element>,
            ParserError,
        >,
        op: Op,
        right: Term<E>,
        set: E,
    ) -> Result<Term<E>, ParserError> {
        match op {
            Op::Subtract => Ok(current - right),
            Op::Divide => Ok(current / right),
            _ => apply_semiring_binary(current, current_in_coefficient_set, op, right, set),
        }
    }
}

impl<E: Semiring> ParseBinary<E> for Parser<'_> {
    fn parse_binary_expr(
        &mut self,
        current: Term<E>,
        current_in_coefficient_set: Result<
            Option<<<E as Set>::ProductCoefficientSet as Set>::Element>,
            ParserError,
        >,
        op: Op,
        set: E,
    ) -> Result<(Term<E>, bool), ParserError> {
        if Op::Pow == op {
            if let Some(right) = ParseExpression::<E::ExponantSet>::parse_expression(
                self,
                op.get_priority() - 1,
                set.get_exponant_set(),
            )? {
                <Self as CheckExponent<E>>::check_exponent(&right)?;
                return Ok((current.pow(&right), true));
            }
        } else if let Some(right) =
            ParseExpression::<E>::parse_expression(self, op.get_priority(), set)?
        {
            return Ok((
                <Self as ApplyBinary<E>>::apply_binary(
                    current,
                    current_in_coefficient_set,
                    op,
                    right,
                    set,
                )?,
                true,
            ));
        }
        Ok((current, false))
    }
}
impl Parser<'_> {
    fn parse_literal_term<E: SetParseExpression>(
        &mut self,
        set: E,
    ) -> Result<Option<Term<E>>, ParserError> {
        Ok(self
            .parse_literal(set)?
            .map(|lit| Term::Value(Value::new(lit, set))))
    }
    /// Parse a literal living in the set `E`.
    ///
    /// ```rust
    /// use formalith::{field::{real::R, matrix::M}, parser::Parser};
    ///
    /// let mut parser = Parser::new("42/1700");
    /// let n = parser.parse_literal(R);
    /// assert_eq!(n, Ok(Some(42.into())));
    /// ```
    ///
    /// # Errors
    /// This method can return an error if the parsing failed.
    pub fn parse_literal<E: SetParseExpression>(
        &mut self,
        set: E,
    ) -> Result<Option<E::Element>, ParserError> {
        set.parse_literal(self).map_err(ParserError::new)
    }
    /// Calls `f` if the current token is a literal, and advance token if `f`. Returns `Ok(None)` otherwise.
    ///
    /// ```rust
    /// use formalith::parser::Parser;
    ///
    /// let mut parser = Parser::new("5 + 3");
    /// let n = parser.is_literal_and(|x| {
    ///     assert_eq!(x, "5");
    ///     x.parse()
    ///         .map_err(|_| "failed to parse the literal".to_owned())
    ///         .map(Some)
    /// });
    /// assert_eq!(n, Ok(Some(5)));
    /// ```
    ///
    /// # Errors
    /// This method can return an error if the parsing failed.
    pub fn is_literal_and<E, F: Fn(&str) -> Result<Option<E>, String>>(
        &mut self,
        f: F,
    ) -> Result<Option<E>, String> {
        let content = &self.input[self.span()];
        match &self.token.kind {
            TokenKind::Literal { .. } => Ok(f(content)?.inspect(|_| self.next_token())),
            _ => Ok(None),
        }
    }
}

trait ParseUnary<E: Set> {
    fn parse_unary(&mut self, _set: E) -> Result<Option<Term<E>>, ParserError>;
}

impl<E: Set> ParseUnary<E> for Parser<'_> {
    default fn parse_unary(&mut self, _set: E) -> Result<Option<Term<E>>, ParserError> {
        Ok(None)
    }
}

impl<E: Monoid> ParseUnary<E> for Parser<'_> {
    default fn parse_unary(&mut self, set: E) -> Result<Option<Term<E>>, ParserError> {
        match self.get_op() {
            Some(Op::Add) => {
                self.next_token();
                ParseExpression::<E>::parse_expression(self, Op::Multiply.get_priority(), set)
            }
            Some(Op::Subtract) => Err(ParserError::new(
                "negation isn't defined in this set, which has no additive inverses",
            )),
            _ => Ok(None),
        }
    }
}

impl<E: Group> ParseUnary<E> for Parser<'_> {
    fn parse_unary(&mut self, set: E) -> Result<Option<Term<E>>, ParserError> {
        match self.get_op() {
            Some(Op::Add) => {
                self.next_token();
                ParseExpression::<E>::parse_expression(self, Op::Multiply.get_priority(), set)
            }
            Some(Op::Subtract) => {
                self.next_token();
                Ok(
                    ParseExpression::<E>::parse_expression(self, Op::Multiply.get_priority(), set)?
                        .map(|term| -term),
                )
            }
            _ => Ok(None),
        }
    }
}

/// Try parsing the given input inside the given set, returning a `Result`. See [`crate::parse`].
#[macro_export(local_inner_macros)]
macro_rules! try_parse {
    ( $x:expr, $f:expr ) => {
        $crate::parser::Parser::new($x.as_ref()).parse($f)
    };
    ( $x:expr, $f:expr, $env:expr ) => {
        $crate::parser::Parser::new($x.as_ref())
            .with_environment($env)
            .parse($f)
    };
}

/// Parse the given input inside the given set, panic if it is incorrect.
#[macro_export(local_inner_macros)]
macro_rules! parse {
    ( $($args:tt)* ) => {
        try_parse!($($args)*).unwrap()
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        field::real::R,
        term::{
            Add,
            flags::{Flags, NORMALIZED},
        },
    };

    #[test]
    fn test_parse_args() {
        let mut parser = Parser::new("5, 7");
        let args = parser.parse_args(R);
        assert_eq!(args, Ok(vec![5.into(), 7.into()]));
    }
    #[test]
    fn test_parse_function() {
        // Function calls are evaluated once parsed
        let mut parser = Parser::new("abs(-5)");
        let args = ParseExpression::<_>::parse_expression(&mut parser, 0, R);
        assert_eq!(args, Ok(Some(5.into())));
        let mut parser = Parser::new("det(1)");
        let args = ParseExpression::<_>::parse_expression(&mut parser, 0, R);
        assert_eq!(args, Ok(Some(1.into())));
    }
    #[test]
    fn test_parse_unary() {
        let mut parser = Parser::new("-5");
        let args = ParseUnary::<_>::parse_unary(&mut parser, R);
        assert_eq!(args, Ok(Some((-5).into())));

        let mut parser = Parser::new("+5");
        let args = ParseUnary::<_>::parse_unary(&mut parser, R);
        assert_eq!(args, Ok(Some(5.into())));
    }
    #[test]
    fn test_parse_binary() {
        let mut parser = Parser::new("x");
        let args = ParseBinary::<_>::parse_binary_expr(
            &mut parser,
            5.into(),
            Err(ParserError::new("unreachable")),
            Op::Add,
            R,
        );

        let mut add = Term::Add(Add::new(
            vec![SymbolTerm::new(Symbol::new("x"), R).into(), 5.into()],
            R,
        ));
        add.add_flag(NORMALIZED);
        assert_eq!(args, Ok((add, true)));

        let mut parser = Parser::new("6");
        let args = ParseBinary::<_>::parse_binary_expr(
            &mut parser,
            5.into(),
            Err(ParserError::new("unreachable")),
            Op::Pow,
            R,
        );

        assert_eq!(args, Ok((15625.into(), true)));

        let mut parser = Parser::new("6");
        let args = ParseBinary::<_>::parse_binary_expr(
            &mut parser,
            5.into(),
            Err(ParserError::new("unreachable")),
            Op::Subtract,
            R,
        );

        assert_eq!(args, Ok(((-1).into(), true)));
    }
}
