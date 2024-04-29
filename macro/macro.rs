//! A proc-macro parser for Minuet programs.
//!
//! Translate Rust tokens into Minuet ones, parse them,
//! and (if successful) emit Rust code that constructs
//! the corresponding AST.

use std::fmt::{self, Display};

use nom::error::ErrorKind;
use proc_macro::{Delimiter, TokenStream, TokenTree};
use proc_macro2::Span;
use quote::{quote, quote_spanned};

use minuet_syntax::{
    Lex as _, Minuet1Lexer, Minuet1Parser, Minuet1Token, Parse as _, Symbol as Minuet1Symbol,
    Tokens,
};

struct Error {
    message: String,
    span: Span,
}

impl Error {
    fn new(message: String, span: Span) -> Self {
        Self { message, span }
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

type Result<T> = std::result::Result<T, Error>;
type Token = minuet_syntax::Token<Minuet1Token, Span>;

fn delimited(left: Token, middle: Vec<Token>, right: Token) -> Vec<Token> {
    let mut toks = Vec::new();
    toks.push(left);
    toks.extend(middle);
    toks.push(right);
    toks
}

/// Translate a stream of Rust tokens to a sequence of Minuet tokens.
fn translate_tokens(input: TokenStream) -> Result<Vec<Token>> {
    use Minuet1Token::*;
    Ok(input
        .into_iter()
        .map(|tt| {
            Ok(match tt {
                TokenTree::Group(g) => {
                    let open = g.span_open().into();
                    let close = g.span_close().into();
                    match g.delimiter() {
                        Delimiter::Parenthesis => delimited(
                            Token::new(LParen, open),
                            translate_tokens(g.stream())?,
                            Token::new(RParen, close),
                        ),
                        Delimiter::Brace => delimited(
                            Token::new(LBrace, open),
                            translate_tokens(g.stream())?,
                            Token::new(RBrace, close),
                        ),
                        Delimiter::Bracket => delimited(
                            Token::new(LBracket, open),
                            translate_tokens(g.stream())?,
                            Token::new(RBracket, close),
                        ),
                        Delimiter::None => {
                            return Err(Error::new("unexpected delimiter ∅".to_string(), open))
                        }
                    }
                }
                TokenTree::Ident(i) => {
                    let name = i.to_string();
                    let span = i.span().into();
                    vec![Token::new(
                        match name.as_str() {
                            "and" => And,
                            "or" => Or,
                            "not" => Not,
                            "if" => If,
                            _ => Symbol(Minuet1Symbol::new(name)),
                        },
                        span,
                    )]
                }
                TokenTree::Punct(p) => {
                    let span = p.span().into();
                    vec![Token::new(
                        match p.as_char() {
                            // no DotDot, single chars only
                            '.' => Dot,
                            '-' => Dash,
                            '/' => Slash,
                            '*' => Star,
                            '|' => Bar,
                            '!' => Bang,
                            '^' => Caret,
                            ',' => Comma,
                            '%' => Percent,
                            '+' => Plus,
                            '#' => Pound,
                            '?' => Query,
                            ':' => Colon,
                            ';' => Semi,
                            '~' => Tilde,
                            '=' => Eq,
                            // no Ne
                            '<' => Lt,
                            '>' => Gt,
                            // no Leq, Geq
                            // Parens, Brackets, and Braces handled as delimiters above
                            c => {
                                return Err(Error::new(
                                    format!("unexpected punctuation '{c}'"),
                                    span,
                                ))
                            }
                        },
                        span,
                    )]
                }
                TokenTree::Literal(l) => {
                    // There is currently no good way to get the value out of a `proc_macro::Literal`;
                    // see <https://internals.rust-lang.org/t/getting-value-out-of-proc-macro-literal/14140>.
                    // So we use our lexer to re-tokenize the literal's string representation.
                    let s = l.to_string();
                    let span = l.span().into();
                    if s.contains('.') {
                        return Err(Error::new("integers only".to_string(), span));
                    }
                    let (unused, tokens) = Minuet1Lexer::lex(&s)
                        .map_err(|e| Error::new(format!("can't lex literal: {e}"), span))?;
                    match (unused.len(), tokens.len()) {
                        (0, 1) => vec![Token::new(tokens[0].token.clone(), span)],
                        (0, 0) => return Err(Error::new("missing literal".to_string(), span)),
                        (0, _) => return Err(Error::new("too many literals".to_string(), span)),
                        (_, _) => return Err(Error::new(format!("leftover lit: {unused}"), span)),
                    }
                }
            })
        })
        .collect::<Result<Vec<_>>>()?
        .into_iter()
        .flatten()
        .collect())
}

macro_rules! macro_error {
    ($msg: literal) => {{
        let msg = format!($msg);
        quote!(compile_error!(#msg)).into()
    }};
    ($msg: literal, $span: expr) => {{
        let msg = format!($msg);
        quote_spanned!($span=> compile_error!(#msg)).into()
    }};
}

/// Parse `input` as a Minuet program at Rust compile time.
#[proc_macro]
pub fn minuet(input: TokenStream) -> TokenStream {
    match translate_tokens(input) {
        Ok(tokens) => {
            match Minuet1Parser::parse(Tokens::new(&tokens[..])) {
                Ok((unused, minuet_program)) => {
                    if unused.is_empty() {
                        // All input parsed, translate back to Rust tokens.
                        quote!(vec![#(#minuet_program),*] as Vec<BaseRule<Term>>).into()
                    } else {
                        macro_error!(
                            "Minuet tokens left over: {unused:?}",
                            unused.span().expect("no unused elements")
                        )
                    }
                }
                Err(e) => match e {
                    nom::Err::Incomplete(_) => unreachable!("incomplete stream"),
                    nom::Err::Error(e) | nom::Err::Failure(e) => {
                        let c = e.code;
                        macro_error!(
                            "Minuet parsing failed: {c:?}",
                            if let ErrorKind::Eof = c {
                                e.input.span_last().expect("no elements")
                            } else {
                                e.input.span().expect("no elements")
                            }
                        )
                    }
                },
            }
        }
        Err(Error { message, span }) => {
            macro_error!("Minuet lexing failed: {message}", span)
        }
    }
}
