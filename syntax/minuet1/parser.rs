//! Minuet v1 parser.
//!
//! Pratt-style precedence parsing based on Monkey's
//! `parse_pratt_expr` and related routines.

use nom::{
    branch::alt,
    bytes::complete::take,
    combinator::{eof, map, opt, success},
    error::{Error, ErrorKind},
    multi::{separated_list0, separated_list1},
    sequence::{delimited, pair, preceded, terminated, tuple},
    Err, IResult,
};

use crate::{
    parse_token, Aggregate, AggregateBounds, Application, Atom, BaseRule, BinOp, ChoiceRule,
    Constant, Literal, Parse, Pool, Precedence, RelOp, Rule, Symbol, Term, Token, Tokens, UnaryOp,
};

use super::lexer::Minuet1Token;

/// Local alias.
type Input<'a, S> = crate::parser::Input<'a, Minuet1Token, S>;

/// Minuet v1 parser.
pub struct Minuet1Parser;

impl<'a, S: Clone> Parse<'a, S> for Minuet1Parser {
    type Token = Minuet1Token;
    type Tree = BaseRule<Term>;

    /// Parse a stream of Minuet tokens as a sequence of rules.
    /// Semicolons terminate rules, with the last one optional.
    fn parse(input: Input<'a, S>) -> IResult<Input<'a, S>, Vec<Self::Tree>> {
        terminated(separated_list0(end, rule), terminated(opt(end), eof))(input)
    }
}

/// Define a parser combinator that recognizes a single token.
/// Named (mostly) after what they mean, not how they look.
macro_rules! parse_minuet1_token {
    ($function: ident, $token: ident) => {
        parse_token!($function<Minuet1Token>, Minuet1Token::$token);
    };
}

parse_minuet1_token!(dotdot, DotDot);
parse_minuet1_token!(dot, Dot);
parse_minuet1_token!(minus, Dash);
parse_minuet1_token!(over, Slash);
parse_minuet1_token!(times, Star);
parse_minuet1_token!(abs, Bar);
parse_minuet1_token!(exc, Bang);
parse_minuet1_token!(exp, Caret);
parse_minuet1_token!(comma, Comma);
//parse_minuet1_token!(percent, Percent);
parse_minuet1_token!(plus, Plus);
//parse_minuet1_token!(pound, Pound);
//parse_minuet1_token!(query, Query);
//parse_minuet1_token!(colon, Colon);
parse_minuet1_token!(end, Semi);
parse_minuet1_token!(complement, Tilde);
parse_minuet1_token!(and, And);
parse_minuet1_token!(or, Or);
parse_minuet1_token!(not, Not);
parse_minuet1_token!(r#if, If);
parse_minuet1_token!(eq, Eq);
parse_minuet1_token!(ne, Ne);
parse_minuet1_token!(lt, Lt);
parse_minuet1_token!(gt, Gt);
parse_minuet1_token!(leq, Leq);
parse_minuet1_token!(geq, Geq);
parse_minuet1_token!(lparen, LParen);
parse_minuet1_token!(rparen, RParen);
//parse_minuet1_token!(lbracket, LBracket);
//parse_minuet1_token!(rbracket, RBracket);
parse_minuet1_token!(lbrace, LBrace);
parse_minuet1_token!(rbrace, RBrace);

fn constant<S: Clone>(input: Input<S>) -> IResult<Input<S>, Constant> {
    let (input, tokens) = take(1_usize)(input)?;
    if tokens.is_empty() {
        Err(Err::Error(Error::new(input, ErrorKind::Fail)))
    } else {
        match tokens.tok[0].token.clone() {
            Minuet1Token::String(s) => Ok((input, Constant::Name(Symbol::new(s)))),
            Minuet1Token::Integer(i) => Ok((input, Constant::Number(i))),
            _ => Err(Err::Error(Error::new(input, ErrorKind::Fail))),
        }
    }
}

fn symbol<S: Clone>(input: Input<S>) -> IResult<Input<S>, Symbol> {
    let (input, tokens) = take(1_usize)(input)?;
    if tokens.is_empty() {
        Err(Err::Error(Error::new(input, ErrorKind::Fail)))
    } else {
        match tokens.tok[0].token.clone() {
            Minuet1Token::Symbol(s) => Ok((input, s)),
            _ => Err(Err::Error(Error::new(input, ErrorKind::Fail))),
        }
    }
}

fn set<S: Clone>(input: Input<S>) -> IResult<Input<S>, Pool<Term>> {
    map(
        // Must have at least two alternatives for a choice.
        pair(terminated(term, or), separated_list1(or, term)),
        |(first, mut rest)| {
            let mut s = vec![first];
            s.append(&mut rest);
            Pool::set(s)
        },
    )(input)
}

fn pool<S: Clone>(input: Input<S>) -> IResult<Input<S>, Term> {
    map(set, Term::Pool)(input)
}

fn arguments<S: Clone>(input: Input<S>) -> IResult<Input<S>, Vec<Term>> {
    delimited(lparen, separated_list0(comma, alt((pool, term))), rparen)(input)
}

fn application<S: Clone>(input: Input<S>) -> IResult<Input<S>, Application<Term>> {
    let (input, (predicate, arguments)) = pair(symbol, arguments)(input)?;
    Ok((input, Application::new(predicate, arguments)))
}

fn atom<S: Clone>(input: Input<S>) -> IResult<Input<S>, Atom<Term>> {
    // Auxiliaries have no surface syntax, so this alt is not exhaustive.
    alt((
        //map(agg, Atom::Agg),
        map(application, Atom::App),
    ))(input)
}

fn double_negative<S: Clone>(input: Input<S>) -> IResult<Input<S>, Atom<Term>> {
    preceded(pair(not, not), atom)(input)
}

fn negative<S: Clone>(input: Input<S>) -> IResult<Input<S>, Atom<Term>> {
    preceded(not, atom)(input)
}

fn rel_op<S: Clone>(input: Input<S>) -> IResult<Input<S>, RelOp> {
    alt((
        map(alt((leq, preceded(lt, eq))), |_| RelOp::Leq),
        map(alt((geq, preceded(gt, eq))), |_| RelOp::Geq),
        map(alt((ne, preceded(exc, eq))), |_| RelOp::Ne),
        map(lt, |_| RelOp::Lt),
        map(gt, |_| RelOp::Gt),
        map(eq, |_| RelOp::Eq),
    ))(input)
}

fn relation<S: Clone>(input: Input<S>) -> IResult<Input<S>, (Term, RelOp, Term)> {
    tuple((term, rel_op, term))(input)
}

fn literal<S: Clone>(input: Input<S>) -> IResult<Input<S>, Literal<Term>> {
    alt((
        delimited(lparen, literal, rparen),
        map(double_negative, Literal::DoubleNegative),
        map(negative, Literal::Negative),
        map(relation, |(l, op, r)| Literal::relation(l, op, r)),
        map(atom, Literal::Positive),
    ))(input)
}

fn upto<S: Clone>(input: Input<S>) -> IResult<Input<S>, Input<S>> {
    // The proc-macro lexer can't emit `DotDot` because it gets the dots one
    // at a time and we don't currently post-process them. So treat two `Dot`s
    // in a row as equivalent to `DotDot`.
    alt((dotdot, preceded(dot, dot)))(input)
}

fn bin_op<S: Clone>(input: Input<S>) -> IResult<Input<S>, (Precedence, Option<BinOp>)> {
    alt((
        map(upto, |_| (Precedence::Interval, None)),
        map(minus, |_| (Precedence::Subtraction, Some(BinOp::Sub))),
        map(plus, |_| (Precedence::Addition, Some(BinOp::Add))),
        map(over, |_| (Precedence::Division, Some(BinOp::Div))),
        map(times, |_| (Precedence::Multiplication, Some(BinOp::Mul))),
        map(exp, |_| (Precedence::Exponentiation, Some(BinOp::Exp))),
        success((Precedence::Lowest, None)),
    ))(input)
}

fn infix<S: Clone>(input: Input<S>, left: Term) -> IResult<Input<S>, Term> {
    let (input, (precedence, bin_op)) = bin_op(input)?;
    match (precedence, bin_op) {
        (_, Some(op)) => {
            let (input, right) = pratt_left(input, precedence)?;
            Ok((input, Term::binary_operation(left, op, right)))
        }
        (Precedence::Interval, None) => {
            let (input, right) = pratt_left(input, precedence)?;
            Ok((input, Term::Pool(Pool::interval(left, right))))
        }
        (_, None) => Err(Err::Error(Error::new(input, ErrorKind::Fail))),
    }
}

fn pratt_right<S: Clone>(
    input: Input<S>,
    precedence: Precedence,
    left: Term,
) -> IResult<Input<S>, Term> {
    let (_, (peek, _)) = bin_op(input.clone())?;
    if peek > precedence || (peek == precedence && peek.is_right_assoc()) {
        let (input, left) = infix(input, left)?;
        pratt_right(input, precedence, left)
    } else {
        Ok((input, left))
    }
}

fn pratt_left<S: Clone>(input: Input<S>, precedence: Precedence) -> IResult<Input<S>, Term> {
    let (input, left) = base_term(input)?;
    pratt_right(input, precedence, left)
}

fn binary_operation<S: Clone>(input: Input<S>) -> IResult<Input<S>, Term> {
    pratt_left(input, Precedence::Lowest)
}

fn unary_operation<S: Clone>(input: Input<S>) -> IResult<Input<S>, Term> {
    use UnaryOp::*;
    fn unary_op(op: UnaryOp) -> Box<dyn Fn(Term) -> Term> {
        Box::new(move |term| -> Term { Term::unary_operation(op, term) })
    }
    alt((
        map(delimited(abs, term, abs), unary_op(Abs)),
        map(preceded(minus, base_term), unary_op(Neg)),
        map(preceded(complement, base_term), unary_op(Not)),
    ))(input)
}

fn base_term<S: Clone>(input: Input<S>) -> IResult<Input<S>, Term> {
    alt((
        unary_operation,
        delimited(lparen, term, rparen),
        map(constant, Term::Constant),
        map(symbol, Term::Variable),
    ))(input)
}

fn term<S: Clone>(input: Input<S>) -> IResult<Input<S>, Term> {
    alt((
        map(application, Term::Function),
        binary_operation,
        base_term,
    ))(input)
}

fn head<S: Clone>(input: Input<S>) -> IResult<Input<S>, Vec<Literal<Term>>> {
    separated_list1(or, literal)(input)
}

fn body<S: Clone>(input: Input<S>) -> IResult<Input<S>, Vec<Literal<Term>>> {
    separated_list0(and, literal)(input)
}

fn disjunctive_rule<S: Clone>(input: Input<S>) -> IResult<Input<S>, BaseRule<Term>> {
    map(
        alt((
            pair(head, preceded(r#if, body)),
            map(preceded(r#if, body), |body| (Vec::new(), body)),
            map(head, |head| (head, Vec::new())),
        )),
        |(head, body)| BaseRule::Disjunctive(Rule::new(head, body)),
    )(input)
}

fn choice_elements<S: Clone>(input: Input<S>) -> IResult<Input<S>, Vec<Literal<Term>>> {
    separated_list1(or, literal)(input)
}

fn choices<S: Clone>(input: Input<S>) -> IResult<Input<S>, Vec<Literal<Term>>> {
    delimited(lbrace, choice_elements, rbrace)(input)
}

fn choice_head_no_bounds<S: Clone>(input: Input<S>) -> IResult<Input<S>, Aggregate<Term>> {
    map(choices, |choices| Aggregate::new(choices, None))(input)
}

fn choice_head_both_bounds<S: Clone>(input: Input<S>) -> IResult<Input<S>, Aggregate<Term>> {
    map(tuple((term, choices, term)), |(lb, choices, ub)| {
        Aggregate::new(choices, Some(AggregateBounds::new(lb, ub)))
    })(input)
}

fn choice_head<S: Clone>(input: Input<S>) -> IResult<Input<S>, Aggregate<Term>> {
    alt((choice_head_both_bounds, choice_head_no_bounds))(input)
}

fn choice_rule<S: Clone>(input: Input<S>) -> IResult<Input<S>, BaseRule<Term>> {
    map(
        alt((
            pair(choice_head, preceded(r#if, body)),
            map(choice_head, |head| (head, Vec::new())),
        )),
        |(head, body)| BaseRule::Choice(ChoiceRule::new(head, body)),
    )(input)
}

fn rule<S: Clone>(input: Input<S>) -> IResult<Input<S>, BaseRule<Term>> {
    alt((choice_rule, disjunctive_rule))(input)
}

#[cfg(test)]
mod test {
    use crate::*;

    use super::*;

    fn eof<'a>() -> Tokens<'a, Token<Minuet1Token, ()>> {
        Tokens::new(&[])
    }

    macro_rules! tok {
        ($t: literal) => {
            Token::new($t.into(), ())
        };
        ($t: ident) => {
            Token::new(Minuet1Token::$t, ())
        };
        ([$s: ident]) => {
            Token::new(Minuet1Token::Symbol(stringify!($s).into()), ())
        };
    }

    macro_rules! toks {
        [$($t: tt),* $(,)?] => {
            Tokens::new(&[$(tok!($t)),*])
        };
    }

    macro_rules! assert_parse {
        ($parsed: expr, $expected: expr) => {
            assert_eq!($parsed, Ok((eof(), $expected)));
        };
    }

    #[test]
    fn app() {
        assert_parse!(literal(toks![[p], LParen, RParen]), pos!(p()));
    }

    #[test]
    fn app_app() {
        assert_parse!(
            literal(toks![[p], LParen, [q], LParen, RParen, RParen]),
            pos!(p(q()))
        );
    }

    #[test]
    fn eq() {
        assert_parse!(literal(toks![0, Eq, 0]), rel!(0, Eq, 0));
    }

    #[test]
    fn abs() {
        assert_parse!(term(toks![Bar, 1, Bar]), unary!(Abs, 1));
    }

    #[test]
    fn neg() {
        assert_parse!(term(toks![Dash, 1]), unary!(Neg, 1));
    }

    #[test]
    fn not() {
        assert_parse!(term(toks![Tilde, 1]), unary!(Not, 1));
    }

    #[test]
    fn add() {
        assert_parse!(term(toks![1, Plus, 2]), binary!(1, Add, 2));
    }

    #[test]
    fn add_add() {
        // left associative
        assert_parse!(
            term(toks![1, Plus, 2, Plus, 3]),
            binary!(binary!(1, Add, 2), Add, 3)
        );
        // override with parenthesis
        assert_parse!(
            term(toks![1, Plus, LParen, 2, Plus, 3, RParen]),
            binary!(1, Add, binary!(2, Add, 3))
        );
    }

    #[test]
    fn add_neg() {
        assert_parse!(
            term(toks![1, Plus, Dash, 2]),
            binary!(1, Add, unary!(Neg, 2))
        );
    }

    #[test]
    fn add_sub() {
        assert_parse!(
            term(toks![1, Plus, 2, Dash, 3]),
            binary!(binary!(1, Add, 2), Sub, 3)
        );
    }

    #[test]
    fn add_mul() {
        assert_parse!(
            term(toks![1, Plus, 2, Star, 3]),
            binary!(1, Add, binary!(2, Mul, 3))
        );
    }

    #[test]
    fn add_mul_add() {
        assert_parse!(
            term(toks![2, Plus, 3, Star, 4, Plus, 5]),
            binary!(binary!(2, Add, binary!(3, Mul, 4)), Add, 5)
        );
    }

    #[test]
    fn mul_add() {
        assert_parse!(
            term(toks![3, Star, 2, Plus, 1]),
            binary!(binary!(3, Mul, 2), Add, 1)
        );
    }

    #[test]
    fn exp() {
        assert_parse!(term(toks![2, Caret, 3]), binary!(2, Exp, 3));
    }

    #[test]
    fn exp_add() {
        assert_parse!(
            term(toks![2, Caret, 3, Plus, 1]),
            binary!(binary!(2, Exp, 3), Add, 1)
        );
        assert_parse!(
            term(toks![1, Plus, 2, Caret, 3]),
            binary!(1, Add, binary!(2, Exp, 3))
        );
    }

    #[test]
    fn exp_mul() {
        assert_parse!(
            term(toks![2, Caret, 3, Star, 4]),
            binary!(binary!(2, Exp, 3), Mul, 4)
        );
        assert_parse!(
            term(toks![2, Caret, LParen, 3, Star, 4, RParen]),
            binary!(2, Exp, binary!(3, Mul, 4))
        );
    }

    #[test]
    fn exp_exp() {
        // right associative
        assert_parse!(
            term(toks![2, Caret, 3, Caret, 4]),
            binary!(2, Exp, binary!(3, Exp, 4))
        );
        // override with parenthesis
        assert_parse!(
            term(toks![LParen, 2, Caret, 3, RParen, Caret, 4]),
            binary!(binary!(2, Exp, 3), Exp, 4)
        );
    }

    #[test]
    fn int() {
        assert_parse!(term(toks![0, DotDot, 1]), pool!(0 => 1));
        assert_eq!(term(toks![0, Dot, Dot, 1]), term(toks![0, DotDot, 1]));
    }

    #[test]
    fn neg_int() {
        assert_parse!(term(toks![Dash, 3, DotDot, 1]), pool!(unary!(Neg, 3) => 1));
    }
}
