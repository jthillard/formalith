//! Lexer part of the parser.

use std::{fmt::Display, str::Chars};

/// A token produced by the lexer.
#[derive(Debug, Clone)]
pub struct Token {
    /// Its kind
    pub kind: TokenKind,
    /// Its character's length,
    pub len: usize,
}

impl Token {
    /// Create a new token
    #[must_use]
    pub const fn new(kind: TokenKind, len: usize) -> Self {
        Self { kind, len }
    }
}

/// Describe the type of the token.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TokenKind {
    /// A space
    Whitespace,

    /// (
    OpenParen,
    /// )
    CloseParen,
    /// [
    OpenBracket,
    /// ]
    CloseBracket,
    /// {
    OpenBrace,
    /// }
    CloseBrace,
    /// An identifier
    Ident(String),

    /// +
    Plus,
    /// -
    Minus,
    /// *
    Star,
    /// /
    Slash,
    /// ^
    Caret,

    /// A literal, which can be of any kind in [`LiteralTokenKind`]
    Literal {
        /// Its kind
        kind: LiteralTokenKind,
    },

    /// ,
    Comma,
    /// :=
    Define,
    /// End Of File
    Eof,
    /// Unknown character
    Unknown,
}

/// Describe the type of a literal
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LiteralTokenKind {
    /// An integer
    Int,
    /// A float number
    Float,
    /// A boolean
    Bool,
}

#[derive(Clone, Debug)]
pub(crate) struct Lexer<'a> {
    len_remaining: usize,
    pos: usize,
    chars: Chars<'a>,
    input: &'a str,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Lexer {
            len_remaining: input.len(),
            chars: input.chars(),
            pos: 0,
            input,
        }
    }
}
impl Lexer<'_> {
    /// Returns amount of already consumed symbols.
    fn pos_within_token(&self) -> usize {
        self.len_remaining - self.chars.as_str().len()
    }

    /// Resets the number of bytes consumed to 0.
    fn reset_pos_within_token(&mut self) {
        self.pos = self.current_pos();
        self.len_remaining = self.chars.as_str().len();
    }

    /// Return the current position in the input string.
    fn current_pos(&self) -> usize {
        self.pos + self.pos_within_token()
    }

    fn peek_char(&self) -> char {
        self.chars.clone().next().unwrap_or('\0')
    }
    fn eof(&self) -> bool {
        self.chars.clone().next().is_none()
    }
    fn lex(&mut self) -> Token {
        // Stop the lexer at the end of the file
        if self.eof() {
            return Token::new(TokenKind::Eof, 0);
        }
        let token_kind = match self.chars.next().unwrap() {
            '/' => TokenKind::Slash,

            c if c.is_ascii_whitespace() => self.consume_whitespaces(),
            '0'..='9' => self.consume_number(),

            '+' => TokenKind::Plus,
            '-' => TokenKind::Minus,

            '*' => TokenKind::Star,
            ',' => TokenKind::Comma,
            ':' if self.peek_char() == '=' => {
                self.chars.next();
                TokenKind::Define
            }
            '^' => TokenKind::Caret,
            '{' => TokenKind::OpenBrace,
            '}' => TokenKind::CloseBrace,
            '(' => TokenKind::OpenParen,
            ')' => TokenKind::CloseParen,
            '[' => TokenKind::OpenBracket,
            ']' => TokenKind::CloseBracket,

            c if c.is_ascii_alphabetic() || c == '_' => self.consume_ident(),
            _ => TokenKind::Unknown,
        };
        let len = self.pos_within_token();
        self.reset_pos_within_token();
        Token::new(token_kind, len)
    }
    fn consume_whitespaces(&mut self) -> TokenKind {
        while self.peek_char().is_ascii_whitespace() {
            self.chars.next();
        }
        TokenKind::Whitespace
    }
    fn consume_number(&mut self) -> TokenKind {
        while self.peek_char().is_ascii_digit() {
            self.chars.next();
        }
        if self.peek_char() == '.' {
            self.chars.next();
            while self.peek_char().is_ascii_digit() {
                self.chars.next();
            }
            TokenKind::Literal {
                kind: LiteralTokenKind::Float,
            }
        } else {
            TokenKind::Literal {
                kind: LiteralTokenKind::Int,
            }
        }
    }
    fn consume_ident(&mut self) -> TokenKind {
        while self.peek_char().is_ascii_alphanumeric() || self.peek_char() == '_' {
            self.chars.next();
        }
        let ident = &self.input[self.pos..self.current_pos()];
        match ident {
            "true" | "false" => TokenKind::Literal {
                kind: LiteralTokenKind::Bool,
            },
            _ => TokenKind::Ident(ident.to_string()),
        }
    }
}

impl Iterator for Lexer<'_> {
    type Item = Token;
    fn next(&mut self) -> Option<Token> {
        let token = self.lex();
        match token.kind {
            TokenKind::Eof => None,
            _ => Some(token),
        }
    }
}

impl Display for Lexer<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let new = self.clone();
        for token in new {
            writeln!(f, "{token:?}")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds(input: &str) -> Vec<TokenKind> {
        Lexer::new(input).map(|token| token.kind).collect()
    }

    fn lengths(input: &str) -> Vec<usize> {
        Lexer::new(input).map(|token| token.len).collect()
    }

    const INT: TokenKind = TokenKind::Literal {
        kind: LiteralTokenKind::Int,
    };
    const FLOAT: TokenKind = TokenKind::Literal {
        kind: LiteralTokenKind::Float,
    };

    #[test]
    fn empty_input() {
        assert!(kinds("").is_empty());
        let mut lexer = Lexer::new("");
        assert_eq!(lexer.lex().kind, TokenKind::Eof);
        assert_eq!(lexer.lex().kind, TokenKind::Eof);
    }

    #[test]
    fn operators_and_delimiters() {
        assert_eq!(
            kinds("+-*/^,()[]{}"),
            vec![
                TokenKind::Plus,
                TokenKind::Minus,
                TokenKind::Star,
                TokenKind::Slash,
                TokenKind::Caret,
                TokenKind::Comma,
                TokenKind::OpenParen,
                TokenKind::CloseParen,
                TokenKind::OpenBracket,
                TokenKind::CloseBracket,
                TokenKind::OpenBrace,
                TokenKind::CloseBrace,
            ]
        );
    }

    #[test]
    fn define() {
        assert_eq!(
            kinds("a:=1"),
            vec![TokenKind::Ident("a".to_string()), TokenKind::Define, INT]
        );
        assert_eq!(lengths("a := 1"), vec![1, 1, 2, 1, 1]);
        // A lone colon is unknown
        assert_eq!(
            kinds(": ="),
            vec![
                TokenKind::Unknown,
                TokenKind::Whitespace,
                TokenKind::Unknown
            ]
        );
    }

    #[test]
    fn numbers() {
        assert_eq!(kinds("42"), vec![INT]);
        assert_eq!(kinds("4.2"), vec![FLOAT]);
        assert_eq!(kinds("4."), vec![FLOAT]);
        assert_eq!(lengths("123 4.56"), vec![3, 1, 4]);
        // A leading dot is not part of a number
        assert_eq!(kinds(".5"), vec![TokenKind::Unknown, INT]);
        // Only one dot per number
        assert_eq!(kinds("1.2.3"), vec![FLOAT, TokenKind::Unknown, INT]);
    }

    #[test]
    fn identifiers() {
        assert_eq!(kinds("x"), vec![TokenKind::Ident("x".to_string())]);
        assert_eq!(
            kinds("x_1 _y abc2"),
            vec![
                TokenKind::Ident("x_1".to_string()),
                TokenKind::Whitespace,
                TokenKind::Ident("_y".to_string()),
                TokenKind::Whitespace,
                TokenKind::Ident("abc2".to_string()),
            ]
        );
        // A number followed by letters is two tokens
        assert_eq!(kinds("2x"), vec![INT, TokenKind::Ident("x".to_string())]);
    }

    #[test]
    fn booleans() {
        let bool_literal = TokenKind::Literal {
            kind: LiteralTokenKind::Bool,
        };
        assert_eq!(
            kinds("true false truex"),
            vec![
                bool_literal.clone(),
                TokenKind::Whitespace,
                bool_literal,
                TokenKind::Whitespace,
                TokenKind::Ident("truex".to_string()),
            ]
        );
    }

    #[test]
    fn whitespaces_are_merged() {
        assert_eq!(
            kinds(" \t\n x  "),
            vec![
                TokenKind::Whitespace,
                TokenKind::Ident("x".to_string()),
                TokenKind::Whitespace
            ]
        );
        assert_eq!(lengths(" \t\n x  "), vec![4, 1, 2]);
    }

    #[test]
    fn unknown_characters() {
        assert_eq!(kinds("@$=!"), vec![TokenKind::Unknown; 4]);
        // Length is counted in bytes
        assert_eq!(lengths("é"), vec![2]);
    }

    #[test]
    fn expression() {
        assert_eq!(
            kinds("abs(x^2-1.5)"),
            vec![
                TokenKind::Ident("abs".to_string()),
                TokenKind::OpenParen,
                TokenKind::Ident("x".to_string()),
                TokenKind::Caret,
                INT,
                TokenKind::Minus,
                FLOAT,
                TokenKind::CloseParen,
            ]
        );
        assert_eq!(lengths("abs(x^2-1.5)").iter().sum::<usize>(), 12);
    }

    #[test]
    fn display() {
        let lexer = Lexer::new("x+1");
        assert_eq!(lexer.to_string().lines().count(), 3);
    }
}
