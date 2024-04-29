//! ASP-Core-2 tokens and tokenizer.

use nom::{branch::alt, combinator::map, multi::many0, sequence::delimited, IResult, InputLength};

use crate::lexer::{integer, space, string, symbol, token, Lex, Token};
use crate::{lex_token, Symbol};

/// Lexical element of an ASP-Core-2 program.
/// See §5: Lexical Matching Table.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AspCore2Token {
    Id(Symbol),
    Variable(Symbol),
    String(String),
    Number(i64),
    AnonymousVariable,
    Dot,
    Comma,
    QueryMark,
    Colon,
    SemiColon,
    Or,
    Naf,
    Cons,
    WCons,
    Plus,
    Minus,
    Times,
    Div,
    At,
    ParenOpen,
    ParenClose,
    SquareOpen,
    SquareClose,
    CurlyOpen,
    CurlyClose,
    Equal,
    Unequal,
    Less,
    Greater,
    LessOrEq,
    GreaterOrEq,
    AggregateCount,
    AggregateMax,
    AggregateMin,
    AggregateSum,
    Minimize,
    Maximize,
    Comment,
    MultiLineComment,
    Blank,
}

impl InputLength for AspCore2Token {
    #[inline]
    fn input_len(&self) -> usize {
        1
    }
}

macro_rules! asp_core2_token {
    ($function: ident, $tag: literal, $token: ident) => {
        lex_token!($function<AspCore2Token>, $tag, AspCore2Token::$token);
    };
}

//asp_core2_token!(anon, "_", AnonymousVariable);
asp_core2_token!(dot, ".", Dot);
asp_core2_token!(comma, ",", Comma);
asp_core2_token!(query, "?", QueryMark);
asp_core2_token!(colon, ":", Colon);
asp_core2_token!(semi, ";", SemiColon);
asp_core2_token!(or, "|", Or);
asp_core2_token!(naf, "not", Naf);
asp_core2_token!(cons, ":-", Cons);
asp_core2_token!(wcons, ":~", WCons);
asp_core2_token!(plus, "+", Plus);
asp_core2_token!(times, "*", Times);
asp_core2_token!(div, "/", Div);
asp_core2_token!(at, "@", At);
asp_core2_token!(paren_open, "(", ParenOpen);
asp_core2_token!(paren_close, ")", ParenClose);
asp_core2_token!(square_open, "[", SquareOpen);
asp_core2_token!(square_close, "]", SquareClose);
asp_core2_token!(curly_open, "{", CurlyOpen);
asp_core2_token!(curly_close, "}", CurlyClose);
asp_core2_token!(equal, "=", Equal);
asp_core2_token!(diamond, "<>", Unequal);
asp_core2_token!(unequal, "!=", Unequal);
asp_core2_token!(less, "<", Less);
asp_core2_token!(greater, ">", Greater);
asp_core2_token!(less_or_eq, "<=", LessOrEq);
asp_core2_token!(greater_or_eq, ">=", GreaterOrEq);
asp_core2_token!(count, "#count", AggregateCount);
asp_core2_token!(max, "#max", AggregateMax);
asp_core2_token!(min, "#min", AggregateMin);
asp_core2_token!(sum, "#sum", AggregateSum);
asp_core2_token!(minimize, "#minimize", Minimize);
asp_core2_token!(maximize, "#maximize", Maximize);

/// ASP-Core-2 lexer.
pub struct AspCore2Lexer;

impl<'a> Lex<'a, &str> for AspCore2Lexer {
    type Input = &'a str;
    type Token = Token<AspCore2Token, &'a str>;

    /// Tokenize a string representation of an ASP-Core-2 program.
    fn lex(input: &'a str) -> IResult<&'a str, Vec<Self::Token>> {
        many0(delimited(
            space, // TODO: alt(comment('%'), space)
            alt((
                token(map(symbol, AspCore2Token::Id)),
                // TODO: Variable
                token(map(string, AspCore2Token::String)),
                token(map(integer, AspCore2Token::Number)),
                cons,
                alt((
                    dot, comma, query, colon, semi, or, naf, cons, wcons, plus, times, div, at,
                )),
                alt((
                    paren_open,
                    paren_close,
                    square_open,
                    square_close,
                    curly_open,
                    curly_close,
                )),
                alt((
                    equal,
                    diamond,
                    unequal,
                    less_or_eq,
                    greater_or_eq,
                    less,
                    greater,
                )),
                alt((count, max, min, sum, minimize, maximize)),
            )),
            space, // TODO: alt(comment('%'), space)
        ))(input)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn asp_core2_lexer() {
        use AspCore2Token::*;

        assert_eq!(AspCore2Lexer::lex(""), Ok(("", vec![])), "nothing");
        assert_eq!(AspCore2Lexer::lex(" "), Ok((" ", vec![])), "whitespace");
        assert_eq!(
            AspCore2Lexer::lex("abc"),
            Ok(("", vec![Token::new(Id("abc".into()), "abc")])),
            "one token"
        );
        assert_eq!(
            AspCore2Lexer::lex("1 {abc} 2 :- do, re, mi."),
            Ok((
                "",
                vec![
                    Token::new(Number(1), "1 {abc} 2 :- do, re, mi."),
                    Token::new(CurlyOpen, "{abc} 2 :- do, re, mi."),
                    Token::new(Id("abc".into()), "abc} 2 :- do, re, mi."),
                    Token::new(CurlyClose, "} 2 :- do, re, mi."),
                    Token::new(Number(2), "2 :- do, re, mi."),
                    Token::new(Cons, ":- do, re, mi."),
                    Token::new(Id("do".into()), "do, re, mi."),
                    Token::new(Comma, ", re, mi."),
                    Token::new(Id("re".into()), "re, mi."),
                    Token::new(Comma, ", mi."),
                    Token::new(Id("mi".into()), "mi."),
                    Token::new(Dot, "."),
                ]
            )),
            "some tokens"
        );
    }
}
