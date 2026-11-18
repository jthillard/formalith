//! Parser implementation, used in [`crate::parse`] and [`crate::try_parse`] macros.

pub mod lexer;

use std::error::Error;
use std::fmt::{Debug, Display};
use std::iter::Peekable;
use std::ops::Range;

use crate::context::{Context, Symbol};
use crate::field::{Group, Ring, Set, SetParseExpression};
use crate::term::{Fun, Mul, Normalize, SymbolTerm, Term, Value};

use lexer::{Lexer, Token, TokenKind};

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Op {
    Add,
    Subtract,
    Multiply,
    Divide,
    Pow,
}
impl Op {
    pub const fn get_priority(&self) -> usize {
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
        };
        parser.next_token();
        parser
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
    /// Return the next operator if it exists and consume it
    const fn get_op(&self) -> Option<Op> {
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
        let term = ParseExpression::<E>::parse_expression(self, 0, set)?
            .ok_or_else(|| ParserError::new("Input was empty"))?;
        if let Some(op) = self.get_op() {
            return Err(ParserError::new(format!(
                "Operand expected for binary operation {op:?} at position {}",
                self.end_span
            )));
        }
        if self.token.kind != TokenKind::Eof {
            return Err(ParserError::new(format!(
                "Unexpected {:?} at position {}",
                self.token.kind, self.start_span
            )));
        }
        Ok(term.normalize())
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
                let content =
                    ParseExpression::<E>::parse_expression(self, 0, set)?.ok_or_else(|| {
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

    /// parse arguments of a function, separated by a comma.
    fn parse_args<E: Set>(&mut self, arg_set: E) -> Result<Vec<Term<E>>, ParserError> {
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
        let mut self_in_coefficient_set = self.clone();
        let node = set.parse_expression(self)?;
        let node = node.map_or_else(|| ParseUnary::<E>::parse_unary(self, set), |n| Ok(Some(n)))?;
        let node_in_coefficient_set =
            self_in_coefficient_set.parse_literal(set.get_coefficient_set());
        let node = node.map_or_else(|| self.parse_literal_term(set), |n| Ok(Some(n)))?;
        let node = node.or_else(|| self.parse_symbol(set));
        let node = node.map_or_else(|| self.parse_group(set), |n| Ok(Some(n)))?;

        match (node, node_in_coefficient_set) {
            (None, Err(_) | Ok(None)) => Ok(None),
            (Some(mut node), mut node_in_coefficient_set) => {
                if let (TokenKind::OpenParen, Term::Symbol(symbol)) = (&self.token.kind, &node) {
                    self.next_token();
                    let ident = symbol.symbol;
                    let (fun, args_count): (Term<E>, _) = match ident {
                        Context::DET => {
                            let args = self.parse_args(set.get_matrix_argument_set())?;
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
                    if matches!(
                        ident,
                        Context::ABS
                            | Context::DET
                            | Context::EXPAND
                            | Context::FACTOR
                            | Context::SIMPLIFY
                            | Context::RE
                            | Context::IM
                            | Context::CONJ
                    ) && args_count != 1
                    {
                        return Err(ParserError::new(format!(
                            "Function {} expects 1 argument, found {args_count}",
                            Context::get_symbol_data(&ident).name
                        )));
                    }
                    node = fun.normalize();
                }
                let mut op = self.get_op();
                while self.token.kind != TokenKind::Eof
                    && op.is_some()
                    && priority < op.as_ref().unwrap().get_priority()
                {
                    let before_op = self.clone();
                    self.next_token();
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

impl<E: Ring> ParseBinary<E> for Parser<'_> {
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
                op.get_priority(),
                set.get_exponant_set(),
            )? {
                return Ok((current.pow(&right), true));
            }
        } else if let Some(right) =
            ParseExpression::<E>::parse_expression(self, op.get_priority(), set)?
        {
            return Ok((
                match op {
                    Op::Add => current + right,
                    Op::Subtract => current - right,
                    Op::Multiply => {
                        if let Ok(Some(current)) = current_in_coefficient_set {
                            Term::Mul(Mul::new(current, vec![right], set)).normalize()
                        } else {
                            current * right
                        }
                    }
                    Op::Divide => current / right,
                    Op::Pow => unreachable!(),
                },
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
