//! ASP-Core-2 parser.

use std::fmt::Debug;

use nom::IResult;

use crate::{BaseRule, Minuet1Token, Parse, Term, Token, Tokens};

/// ASP-Core-2 parser.
pub struct AspCore2Parser;

impl<'a, S: Clone + Debug> Parse<'a, S> for AspCore2Parser {
    type Token = Minuet1Token;
    type Tree = BaseRule<Term>;

    fn parse(
        input: Tokens<'a, Token<Self::Token, S>>,
    ) -> IResult<Tokens<'a, Token<Self::Token, S>>, Vec<Self::Tree>> {
        todo!("parse ASP-Core-2 tokens {input:?}")
    }
}
