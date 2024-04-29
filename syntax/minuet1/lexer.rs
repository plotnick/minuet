//! Minuet v1 tokens and tokenizer.

use nom::{branch::alt, combinator::map, multi::many0, sequence::delimited, IResult, InputLength};

use crate::lexer::{integer, space, string, symbol, token, Lex, Token};
use crate::{lex_token, Symbol};

/// Lexical element of a Minuet v1 program.
/// Named after how they look, not what they mean.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Minuet1Token {
    Symbol(Symbol),
    String(String),
    Integer(i64),
    DotDot,
    Dot,
    Dash,
    Slash,
    Star,
    Bar,
    Bang,
    Caret,
    Comma,
    Percent,
    Plus,
    Pound,
    Query,
    Colon,
    Semi,
    Tilde,
    And,
    Or,
    Not,
    If,
    Eq,
    Ne,
    Lt,
    Gt,
    Leq,
    Geq,
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
}

impl From<Symbol> for Minuet1Token {
    fn from(s: Symbol) -> Self {
        Self::Symbol(s)
    }
}

impl From<&str> for Minuet1Token {
    fn from(s: &str) -> Self {
        Self::String(String::from(s))
    }
}

impl From<i64> for Minuet1Token {
    fn from(i: i64) -> Self {
        Self::Integer(i)
    }
}

impl InputLength for Minuet1Token {
    #[inline]
    fn input_len(&self) -> usize {
        1
    }
}

macro_rules! minuet1_token {
    ($function: ident, $tag: literal, $token: ident) => {
        lex_token!($function<Minuet1Token>, $tag, Minuet1Token::$token);
    };
}

minuet1_token!(dotdot, "..", DotDot);
minuet1_token!(dot, ".", Dot);
minuet1_token!(dash, "-", Dash);
minuet1_token!(slash, "/", Slash);
minuet1_token!(star, "*", Star);
minuet1_token!(bar, "|", Bar);
minuet1_token!(bang, "!", Bang);
minuet1_token!(caret, "^", Caret);
minuet1_token!(comma, ",", Comma);
minuet1_token!(percent, "%", Percent);
minuet1_token!(plus, "+", Plus);
//minuet1_token!(pound, "#", Pound);
minuet1_token!(query, "?", Query);
minuet1_token!(colon, ":", Colon);
minuet1_token!(semi, ";", Semi);
minuet1_token!(tilde, "~", Tilde);
minuet1_token!(and, "and", And);
minuet1_token!(or, "or", Or);
minuet1_token!(not, "not", Not);
minuet1_token!(r#if, "if", If);
minuet1_token!(eq, "=", Eq);
minuet1_token!(ne, "!=", Ne);
minuet1_token!(leq, "<=", Leq);
minuet1_token!(geq, ">=", Geq);
minuet1_token!(lt, "<", Lt);
minuet1_token!(gt, ">", Gt);
minuet1_token!(lparen, "(", LParen);
minuet1_token!(rparen, ")", RParen);
minuet1_token!(lbracket, "[", LBracket);
minuet1_token!(rbracket, "]", RBracket);
minuet1_token!(lbrace, "{", LBrace);
minuet1_token!(rbrace, "}", RBrace);

/// Minuet v1 lexer.
pub struct Minuet1Lexer;

impl<'a> Lex<'a, &str> for Minuet1Lexer {
    type Input = &'a str;
    type Token = Token<Minuet1Token, &'a str>;

    /// Tokenize a string representation of a Minuet program.
    fn lex(input: &'a str) -> IResult<&'a str, Vec<Self::Token>> {
        many0(delimited(
            space, // TODO: alt(comment('#'), space)
            alt((
                alt((and, or, not, r#if)),
                alt((eq, ne, leq, geq, lt, gt)),
                alt((lparen, rparen, lbracket, rbracket, lbrace, rbrace)),
                alt((
                    dotdot, dot, dash, slash, star, bar, bang, caret, comma, percent, plus, query,
                    colon, semi, tilde,
                )),
                token(map(integer, Minuet1Token::Integer)),
                token(map(string, Minuet1Token::String)),
                token(map(symbol, Minuet1Token::Symbol)),
            )),
            space, // TODO: alt(comment('#'), space)
        ))(input)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn minuet1_lexer() {
        use Minuet1Token::*;

        assert_eq!(Minuet1Lexer::lex(""), Ok(("", vec![])), "nothing");
        assert_eq!(Minuet1Lexer::lex(" "), Ok((" ", vec![])), "space");
        assert_eq!(
            Minuet1Lexer::lex("abc"),
            Ok(("", vec![Token::new(Symbol("abc".into()), "abc")])),
            "one token"
        );
        assert_eq!(
            Minuet1Lexer::lex("abc 123"),
            Ok((
                "",
                vec![
                    Token::new(Symbol("abc".into()), "abc 123"),
                    Token::new(Integer(123), "123")
                ]
            )),
            "two tokens"
        );
        assert_eq!(
            Minuet1Lexer::lex("abc 123 \"do re mi\""),
            Ok((
                "",
                vec![
                    Token::new(Symbol("abc".into()), "abc 123 \"do re mi\""),
                    Token::new(Integer(123), "123 \"do re mi\""),
                    Token::new(String("do re mi".to_string()), "\"do re mi\"")
                ]
            )),
            "three tokens"
        );
        assert_eq!(
            Minuet1Lexer::lex("(abc 123)"),
            Ok((
                "",
                vec![
                    Token::new(LParen, "(abc 123)"),
                    Token::new(Symbol("abc".into()), "abc 123)"),
                    Token::new(Integer(123), "123)"),
                    Token::new(RParen, ")")
                ]
            )),
            "parenthesized tokens"
        );
        assert_eq!(
            Minuet1Lexer::lex("[1]"),
            Ok((
                "",
                vec![
                    Token::new(LBracket, "[1]"),
                    Token::new(Integer(1), "1]"),
                    Token::new(RBracket, "]")
                ]
            )),
            "brackets"
        );
        assert_eq!(
            Minuet1Lexer::lex("{2}"),
            Ok((
                "",
                vec![
                    Token::new(LBrace, "{2}"),
                    Token::new(Integer(2), "2}"),
                    Token::new(RBrace, "}")
                ]
            )),
            "braces"
        );
        assert_eq!(
            Minuet1Lexer::lex("-1"),
            Ok((
                "",
                vec![Token::new(Dash, "-1"), Token::new(Integer(1), "1")]
            )),
            "unary -"
        );
        assert_eq!(
            Minuet1Lexer::lex("2^3"),
            Ok((
                "",
                vec![
                    Token::new(Integer(2), "2^3"),
                    Token::new(Caret, "^3"),
                    Token::new(Integer(3), "3")
                ]
            )),
            "exp"
        );
        assert_eq!(
            Minuet1Lexer::lex("1 < 2"),
            Ok((
                "",
                vec![
                    Token::new(Integer(1), "1 < 2"),
                    Token::new(Lt, "< 2"),
                    Token::new(Integer(2), "2")
                ]
            )),
            "<"
        );
        assert_eq!(
            Minuet1Lexer::lex("2 > 1"),
            Ok((
                "",
                vec![
                    Token::new(Integer(2), "2 > 1"),
                    Token::new(Gt, "> 1"),
                    Token::new(Integer(1), "1")
                ]
            )),
            ">"
        );
        assert_eq!(
            Minuet1Lexer::lex("1 <= 2"),
            Ok((
                "",
                vec![
                    Token::new(Integer(1), "1 <= 2"),
                    Token::new(Leq, "<= 2"),
                    Token::new(Integer(2), "2")
                ]
            )),
            "<="
        );
        assert_eq!(
            Minuet1Lexer::lex("2 >= 1"),
            Ok((
                "",
                vec![
                    Token::new(Integer(2), "2 >= 1"),
                    Token::new(Geq, ">= 1"),
                    Token::new(Integer(1), "1")
                ]
            )),
            ">="
        );
        assert_eq!(
            Minuet1Lexer::lex("1 and 2"),
            Ok((
                "",
                vec![
                    Token::new(Integer(1), "1 and 2"),
                    Token::new(And, "and 2"),
                    Token::new(Integer(2), "2")
                ]
            )),
            "and"
        );
        assert_eq!(
            Minuet1Lexer::lex("1..2"),
            Ok((
                "",
                vec![
                    Token::new(Integer(1), "1..2"),
                    Token::new(DotDot, "..2"),
                    Token::new(Integer(2), "2")
                ]
            )),
            ".."
        );
    }
}
