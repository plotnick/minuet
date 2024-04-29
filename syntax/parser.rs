//! Parse a stream of tokens with [nom](https://crates.io/crates/nom).

use nom::IResult;

use crate::{Token, Tokens};

/// An input stream to a parser.
pub type Input<'a, T, S> = Tokens<'a, Token<T, S>>;

/// A parser, generic over the source type to support input from,
/// e.g., strings and Rust tokens.
pub trait Parse<'a, S: Clone> {
    /// The lexical (input) token type being parsed.
    type Token: Clone;

    /// The syntax tree (output) type.
    type Tree;

    /// Parse a token stream.
    fn parse(
        input: Input<'a, Self::Token, S>,
    ) -> IResult<Input<'a, Self::Token, S>, Vec<Self::Tree>>;
}

/// Produce a parser combinator that recognizes a literal token.
/// Adapted from Monkey's `tag_token!` macro.
#[macro_export]
macro_rules! parse_token {
    ($function:ident<$ty: ty>, $tag: expr) => {
        fn $function<S: Clone>(
            input: Tokens<Token<$ty, S>>,
        ) -> IResult<Tokens<Token<$ty, S>>, Tokens<Token<$ty, S>>> {
            ::nom::combinator::verify(
                ::nom::bytes::complete::take(1_usize),
                |t: &Tokens<Token<$ty, S>>| t.tok[0].token == $tag,
            )(input)
        }
    };
}
