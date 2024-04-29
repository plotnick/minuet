//! Tokenize a string representation of a program.

#![allow(dead_code)]

use nom::{
    branch::alt,
    bytes::complete::{escaped_transform, tag},
    character::complete::{alpha1, alphanumeric1, char, digit1, hex_digit1, multispace0, none_of},
    combinator::{map, map_res, recognize, value},
    error::ParseError,
    multi::{many0, many0_count, many1},
    sequence::{delimited, pair, preceded, terminated},
    IResult, Parser,
};

use crate::Symbol;

pub(crate) fn space(input: &str) -> IResult<&str, &str> {
    multispace0(input)
}

pub(crate) fn symbol(input: &str) -> IResult<&str, Symbol> {
    let (input, name) = recognize(pair(
        alt((alpha1, tag("_"))),
        many0_count(alt((alphanumeric1, tag("_")))),
    ))(input)?;
    Ok((input, Symbol::new(name.to_owned())))
}

// TODO: remove when escaped_transform handles opt(..).
// Needs investigation, probably related to nom#{1118,1336}.
fn empty_string(input: &str) -> IResult<&str, String> {
    map(tag(r#""""#), |_| String::new())(input)
}

fn quoted_string(input: &str) -> IResult<&str, String> {
    delimited(
        char('"'),
        escaped_transform(
            none_of(r#"\""#), // TODO: opt(none_of(..))
            '\\',
            alt((
                value("\\", tag("\\")),
                value("\"", tag("\"")),
                value("\n", tag("n")),
                value("\r", tag("r")),
                value("\t", tag("t")),
            )),
        ),
        char('"'),
    )(input)
}

pub(crate) fn string(input: &str) -> IResult<&str, String> {
    alt((empty_string, quoted_string))(input)
}

#[allow(clippy::from_str_radix_10)]
fn decimal(input: &str) -> IResult<&str, i64> {
    map_res(
        recognize(many1(terminated(digit1, many0(char('_'))))),
        |digits: &str| i64::from_str_radix(&digits.replace('_', ""), 10),
    )(input)
}

fn hexadecimal(input: &str) -> IResult<&str, i64> {
    map_res(
        preceded(
            alt((tag("0x"), tag("0X"))),
            recognize(many1(terminated(hex_digit1, many0(char('_'))))),
        ),
        |digits: &str| i64::from_str_radix(&digits.replace('_', ""), 16),
    )(input)
}

pub(crate) fn integer(input: &str) -> IResult<&str, i64> {
    alt((hexadecimal, decimal))(input)
}

pub(crate) fn token<I, O, E, F>(mut parser: F) -> impl FnMut(I) -> IResult<I, Token<O, I>, E>
where
    I: Clone,
    O: Clone,
    E: ParseError<I>,
    F: Parser<I, O, E>,
{
    move |input: I| {
        let i = input.clone();
        let (input, t) = parser.parse(input)?;
        Ok((input, Token::new(t, i)))
    }
}

/// Define a parser combinator for a token denoted by a tag.
/// Adpated from Monkey's `syntax!` macro.
#[macro_export]
macro_rules! lex_token {
    ($function: ident<$ty: ty>, $tag: literal, $token: expr) => {
        pub(crate) fn $function(input: &str) -> IResult<&str, $crate::Token<$ty, &str>> {
            $crate::lexer::token(::nom::combinator::map(
                ::nom::bytes::complete::tag($tag),
                |_| $token,
            ))(input)
        }
    };
}

/// A token with source information.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Token<T: Clone, S: Clone> {
    pub token: T,
    pub source: S,
}

impl<T: Clone, S: Clone> Token<T, S> {
    pub fn new(token: T, source: S) -> Self {
        Self { token, source }
    }
}

/// A lexer, a.k.a. lexical analyzer, tokenizer.
pub trait Lex<'a, S> {
    type Input;
    type Token;

    /// Tokenize an input stream.
    fn lex(input: Self::Input) -> IResult<Self::Input, Vec<Self::Token>>;
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn symbol() {
        assert!(super::symbol("").is_err(), "empty");
        assert!(super::symbol("123").is_err(), "symbol starts with a digit");
        assert_eq!(
            super::symbol("_123"),
            Ok(("", Symbol::new(String::from("_123")))),
            "symbol starts with an underscore"
        );
        assert_eq!(
            super::symbol("foo_123"),
            Ok(("", Symbol::new(String::from("foo_123")))),
            "symbol includes an underscore"
        );
    }

    #[test]
    fn string() {
        assert!(super::string(r#""#).is_err(), "empty");
        assert!(super::string(r#""foo"#).is_err(), "unterminated string");
        assert_eq!(
            super::string(r#""""#),
            Ok(("", String::new())),
            "empty string"
        );
        assert_eq!(
            super::string(r#""foo bar""#),
            Ok(("", String::from("foo bar"))),
            "simple string"
        );
        assert_eq!(
            super::string(r#""Foo:\r\n\t\"Foo\\!\"""#),
            Ok(("", String::from("Foo:\r\n\t\"Foo\\!\""))),
            "backslash escapes"
        );
        assert_eq!(
            super::string(r#""🎼Minuet🎵""#),
            Ok(("", String::from("🎼Minuet🎵"))),
            "✨Unicode✨"
        );
    }

    #[test]
    fn integer() {
        assert!(super::integer("").is_err(), "empty");
        assert!(super::integer("X").is_err(), "invalid");
        assert!(super::integer("12_345_678_901_234_567_890").is_err(), "big");
        assert_eq!(super::integer("0"), Ok(("", 0)), "decimal zero");
        assert_eq!(super::integer("123_456"), Ok(("", 123_456)), "decimal");
        assert_eq!(super::integer("0x0"), Ok(("", 0x0)), "hex zero");
        assert_eq!(super::integer("0x1234_abcd"), Ok(("", 0x1234_abcd)), "hex");
    }
}
