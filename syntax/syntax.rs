//! Syntactic elements of a simple ASP-like logic language.
//!
//! See "Abstract Gringo" (2015) by Gebser, et al. and the
//! "ASP-Core-2 Input Language Format" (2012). A string or
//! macro parser may layer whatever surface syntax it likes
//! on top of these elements.

mod asp_core2;
mod lexer;
mod minuet1;
mod parser;
mod tokens;

use std::collections::BTreeSet;
use std::fmt;
use std::ops;

pub use asp_core2::{AspCore2Lexer, AspCore2Parser, AspCore2Token};
pub use lexer::{Lex, Token};
pub use minuet1::{Minuet1Lexer, Minuet1Parser, Minuet1Token};
pub use parser::Parse;
pub use tokens::Tokens;

/// Uninterpreted element that names itself, a predicate, or a variable.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Symbol(String);

impl Symbol {
    pub fn new(name: String) -> Self {
        Symbol(name)
    }

    pub fn name(&self) -> &str {
        &self.0
    }
}

impl From<&str> for Symbol {
    fn from(s: &str) -> Self {
        Symbol::new(String::from(s))
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// Uninterpreted element that represents itself.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Constant {
    Name(Symbol),
    Number(i64),
}

impl From<&str> for Constant {
    fn from(s: &str) -> Self {
        Self::Name(Symbol::from(s))
    }
}

impl From<Symbol> for Constant {
    fn from(s: Symbol) -> Self {
        Self::Name(s)
    }
}

impl From<i64> for Constant {
    fn from(i: i64) -> Self {
        Self::Number(i)
    }
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Name(s) => f.write_fmt(format_args!("{s}")),
            Self::Number(i) => f.write_fmt(format_args!("{i}")),
        }
    }
}

impl ops::Add for Constant {
    type Output = Option<Self>;

    fn add(self, rhs: Self) -> Self::Output {
        use Constant::*;
        match (self, rhs) {
            (Name(_), Number(_)) | (Number(_), Name(_)) => None,
            (Number(x), Number(y)) => Some(Number(x + y)),
            (Name(a), Name(b)) => Some(Name(Symbol::new({
                let mut x = a.name().to_owned();
                x.push_str(b.name());
                x
            }))),
        }
    }
}

impl ops::Sub for Constant {
    type Output = Option<Self>;

    fn sub(self, rhs: Self) -> Self::Output {
        use Constant::*;
        match (self, rhs) {
            (Name(_), Number(_)) | (Number(_), Name(_)) => None,
            (Number(x), Number(y)) => Some(Number(x - y)),
            (Name(a), Name(b)) => a
                .name()
                .strip_suffix(b.name())
                .map(|diff| Name(Symbol::new(String::from(diff)))),
        }
    }
}

impl ops::Mul for Constant {
    type Output = Option<Self>;

    fn mul(self, rhs: Self) -> Self::Output {
        use Constant::*;
        match (self, rhs) {
            (Name(_), Name(_)) => None,
            (Number(x), Number(y)) => Some(Number(x * y)),
            (Name(a), Number(n)) | (Number(n), Name(a)) => Some(Name(Symbol::new({
                let mut x = String::new();
                for _ in 0..n {
                    x.push_str(a.name());
                }
                x
            }))),
        }
    }
}

impl ops::Div for Constant {
    type Output = Option<Self>;

    fn div(self, rhs: Self) -> Self::Output {
        use Constant::*;
        match (self, rhs) {
            (Number(_) | Name(_), Name(_)) => None,
            (Number(_), Number(0)) => None,
            (Number(x), Number(y)) => Some(Number(x / y)),
            (Name(name), Number(number)) => todo!("{name} / {number}"),
        }
    }
}

impl ops::Rem for Constant {
    type Output = Option<Self>;

    fn rem(self, rhs: Self) -> Self::Output {
        use Constant::*;
        match (self, rhs) {
            (Number(_) | Name(_), Name(_)) => None,
            (Number(_), Number(0)) => None,
            (Number(x), Number(y)) => Some(Number(x % y)),
            (Name(name), Number(number)) => todo!("{name} % {number}"),
        }
    }
}

impl ops::Neg for Constant {
    type Output = Option<Self>;

    fn neg(self) -> Self::Output {
        use Constant::*;
        if let Number(x) = self {
            Some(Number(-x))
        } else {
            None
        }
    }
}

impl ops::Not for Constant {
    type Output = Option<Self>;

    fn not(self) -> Self::Output {
        todo!("classical negation")
    }
}

/// Arithmetic operations represented by direct methods
/// instead of `std::ops` traits.
impl Constant {
    /// Absolute value.
    pub fn abs(self) -> Option<Self> {
        use Constant::*;
        if let Number(x) = self {
            Some(Number(x.abs()))
        } else {
            None
        }
    }

    /// Exponentiation.
    pub fn pow(self, exponent: Self) -> Option<Self> {
        use Constant::*;
        if let (Number(base), Number(exponent)) = (self, exponent) {
            if let Ok(exponent) = u32::try_from(exponent) {
                return Some(Number(base.pow(exponent)));
            }
        }
        None
    }
}

/// An interval or arbitrary set of values.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Pool<T> {
    Interval(Box<T>, Box<T>),
    Set(BTreeSet<T>),
}

impl<T> Pool<T>
where
    T: Ord,
{
    pub fn interval(x: impl Into<T>, y: impl Into<T>) -> Self {
        Self::Interval(Box::new(x.into()), Box::new(y.into()))
    }

    pub fn set(elements: impl IntoIterator<Item = T>) -> Self {
        Self::Set(elements.into_iter().collect())
    }
}

impl<T> fmt::Display for Pool<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Interval(i, j) => f.write_fmt(format_args!("{i}..{j}")),
            Self::Set(p) => f.write_fmt(format_args!(
                "{}",
                p.iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
                    .join(" or ")
            )),
        }
    }
}

/// Arithmetic relational operators: equal, not equal, less than,
/// greater than, less than or equal to, greater than or equal to.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum RelOp {
    Eq,
    Ne,
    Lt,
    Gt,
    Leq,
    Geq,
}

impl RelOp {
    pub fn eval<T>(&self, x: T, y: T) -> bool
    where
        T: Eq + Ord,
    {
        use RelOp::*;
        match self {
            Eq => x == y,
            Ne => x != y,
            Lt => x < y,
            Gt => x > y,
            Leq => x <= y,
            Geq => x >= y,
        }
    }

    pub fn negate(self) -> Self {
        use RelOp::*;
        match self {
            Eq => Ne,
            Ne => Eq,
            Lt => Geq,
            Gt => Leq,
            Leq => Gt,
            Geq => Lt,
        }
    }
}

impl fmt::Display for RelOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use RelOp::*;
        f.write_str(match self {
            Eq => "=",
            Ne => "!=",
            Lt => "<",
            Gt => ">",
            Leq => "<=",
            Geq => ">=",
        })
    }
}

/// Unary (prefix) operations: absolute value, numeric negation,
/// and logical (a.k.a., classical, strong) negation.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum UnaryOp {
    Abs,
    Neg,
    Not,
}

/// [Pratt style](https://en.wikipedia.org/wiki/Operator-precedence_parser#Pratt_parsing).
/// precedence parsing.
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
enum Precedence {
    Lowest,
    Interval,
    Subtraction,
    Addition,
    Division,
    Multiplication,
    Exponentiation,
}

impl Precedence {
    fn is_right_assoc(&self) -> bool {
        matches!(self, Precedence::Exponentiation)
    }
}

/// Binary (infix) arithmetic operations: addition, subtraction,
/// multiplication, exponentiation, division, and remainder.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Exp,
    Div,
    Rem,
    //Mod,
}

impl BinOp {
    pub fn eval(&self, x: Constant, y: Constant) -> Option<Constant> {
        use BinOp::*;
        match self {
            Add => x + y,
            Sub => x - y,
            Mul => x * y,
            Exp => x.pow(y),
            Div => x / y,
            Rem => x % y,
        }
    }
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use BinOp::*;
        f.write_str(match self {
            Add => "+",
            Sub => "-",
            Mul => "*",
            Exp => "^",
            Div => "/",
            Rem => "%",
        })
    }
}

/// Interpreted element that represents either itself (a constant),
/// something else (a variable), a choice from a set of values, or
/// an operation applied to a set of values.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Term {
    Constant(Constant),
    Variable(Symbol),
    Pool(Pool<Term>),
    UnaryOperation(UnaryOp, Box<Term>),
    BinaryOperation(Box<Term>, BinOp, Box<Term>),
}

impl Term {
    /// Boxing constructor.
    pub fn unary_operation(op: UnaryOp, x: Term) -> Self {
        Self::UnaryOperation(op, Box::new(x))
    }

    /// Boxing constructor.
    pub fn binary_operation(x: Term, op: BinOp, y: Term) -> Self {
        Self::BinaryOperation(Box::new(x), op, Box::new(y))
    }
}

impl<T: Into<Constant>> From<T> for Term {
    fn from(t: T) -> Self {
        Self::Constant(t.into())
    }
}

impl From<Pool<Term>> for Term {
    fn from(p: Pool<Term>) -> Self {
        Self::Pool(p)
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Term::*;
        use UnaryOp::*;
        match self {
            Constant(x) => x.fmt(f),
            Variable(x) => x.fmt(f),
            Pool(x) => x.fmt(f),
            UnaryOperation(Abs, x) => f.write_fmt(format_args!("|{x}|")),
            UnaryOperation(Neg, x) => f.write_fmt(format_args!("-{x}")),
            UnaryOperation(Not, x) => f.write_fmt(format_args!("~{x}")),
            BinaryOperation(x, op, y) => f.write_fmt(format_args!("({x} {op} {y})")),
        }
    }
}

/// An _auxiliary atom_ is used to represent a rule's truth value.
/// Each auxiliary is given a prefix (for debugging) and a unique
/// (within a program) integer tag.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Auxiliary {
    pub prefix: Symbol,
    pub number: usize,
}

impl fmt::Display for Auxiliary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Auxiliary { prefix, number } = self;
        f.write_fmt(format_args!("{prefix}_{number}"))
    }
}

/// An _aggregate atom_ represents some subsets of a set of values.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Aggregate<T> {
    pub choices: Vec<Literal<T>>,
    pub bounds: Option<AggregateBounds<T>>,
}

impl<T> Aggregate<T> {
    pub fn new(
        choices: impl IntoIterator<Item = Literal<T>>,
        bounds: Option<AggregateBounds<T>>,
    ) -> Self {
        Self {
            choices: choices.into_iter().collect(),
            bounds,
        }
    }
}

impl<T> fmt::Display for Aggregate<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!(
            "{}{{{}}}{}",
            if let Some(AggregateBounds { lower_bound, .. }) = &self.bounds {
                format!("{lower_bound} ")
            } else {
                String::from("")
            },
            self.choices
                .iter()
                .map(|l| l.to_string())
                .collect::<Vec<_>>()
                .join(" or "),
            if let Some(AggregateBounds { upper_bound, .. }) = &self.bounds {
                format!(" {upper_bound}")
            } else {
                String::from("")
            },
        ))
    }
}

/// Cardinality bounds on aggregate subsets.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct AggregateBounds<T> {
    pub lower_bound: Box<T>,
    pub upper_bound: Box<T>,
}

impl<T> AggregateBounds<T> {
    pub fn new(lower_bound: T, upper_bound: T) -> Self {
        Self {
            lower_bound: Box::new(lower_bound),
            upper_bound: Box::new(upper_bound),
        }
    }
}

/// An _n_-ary predicate applied to a tuple of terms.
/// If _n_ = 0, the arguments are usually elided.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Application<T> {
    pub predicate: Symbol,
    pub arguments: Vec<T>,
}

impl<T> Application<T> {
    pub fn new(predicate: Symbol, arguments: impl IntoIterator<Item = T>) -> Self {
        Self {
            predicate,
            arguments: arguments.into_iter().collect(),
        }
    }
}

impl<T> fmt::Display for Application<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Application {
            predicate,
            arguments,
        } = self;
        if arguments.is_empty() {
            predicate.fmt(f)
        } else {
            f.write_fmt(format_args!(
                "{}({})",
                predicate,
                arguments
                    .iter()
                    .map(|arg| arg.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ))
        }
    }
}

/// An _atomic formula_ contains no logical connectives (i.e., `and`, `or`, `not`).
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Atom<T> {
    /// An auxiliary representing a rule.
    Aux(Auxiliary),

    /// All possible subsets of a set of values.
    Agg(Aggregate<T>),

    /// A predicate applied to a set of values.
    App(Application<T>),
}

impl<T> Atom<T>
where
    T: Clone,
{
    pub fn aux(prefix: Symbol, number: usize) -> Self {
        Self::Aux(Auxiliary { prefix, number })
    }

    pub fn agg(
        choices: impl IntoIterator<Item = Literal<T>>,
        bounds: Option<AggregateBounds<T>>,
    ) -> Self {
        Self::Agg(Aggregate::new(choices, bounds))
    }

    pub fn app(predicate: Symbol, arguments: impl IntoIterator<Item = T>) -> Self {
        Self::App(Application::new(predicate, arguments))
    }
}

impl<T> fmt::Display for Atom<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Atom::*;
        match self {
            Aux(aux) => aux.fmt(f),
            Agg(agg) => agg.fmt(f),
            App(app) => app.fmt(f),
        }
    }
}

/// An atomic formula, its single or double negation as failure,
/// or a boolean arithmetic relation (e.g., `1 < 2`). See Lifschitz,
/// "ASP" §5.8 for why triple negation is unnecessary.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Literal<T> {
    Positive(Atom<T>),
    Negative(Atom<T>),
    DoubleNegative(Atom<T>),
    Relation(Box<T>, RelOp, Box<T>),
}

impl<T> Literal<T> {
    /// Boxing constructor.
    pub fn relation(x: T, rel: RelOp, y: T) -> Self {
        Self::Relation(Box::new(x), rel, Box::new(y))
    }

    /// Negation-as-failure semantics.
    pub fn negate(self) -> Self {
        use Literal::*;
        match self {
            Positive(atom) => Negative(atom),
            Negative(atom) => DoubleNegative(atom),
            DoubleNegative(atom) => Negative(atom),
            Relation(x, rel, y) => Relation(x, rel.negate(), y),
        }
    }

    pub fn is_positive(&self) -> bool {
        matches!(self, Self::Positive(..))
    }

    pub fn is_negative(&self) -> bool {
        !self.is_positive()
    }
}

impl<T> fmt::Display for Literal<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Literal::*;
        match self {
            Positive(atom) => f.write_fmt(format_args!("{}", atom)),
            Negative(atom) => f.write_fmt(format_args!("not {}", atom)),
            DoubleNegative(atom) => f.write_fmt(format_args!("not not {}", atom)),
            Relation(x, rel, y) => f.write_fmt(format_args!("{x} {rel} {y}")),
        }
    }
}

/// Prior to preprocessing, rules come in two basic flavors: _choice_ and
/// _disjunctive_. The head of a choice rule like `{a; b; c}` denotes all
/// possible ways of choosing which of the atoms `a`, `b`, and `c` are
/// included in the model. The head of a disjunctive rule like `a or b or c`
/// instead means that any of the three atoms `a`, `b`, or `c` may be in
/// the model.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BaseRule<T> {
    Choice(ChoiceRule<T>),
    Disjunctive(Rule<T>),
}

impl<T> fmt::Display for BaseRule<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Choice(rule) => rule.fmt(f),
            Self::Disjunctive(rule) => rule.fmt(f),
        }
    }
}

/// A choice rule has a single aggregate atom as its head.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ChoiceRule<T> {
    pub head: Aggregate<T>,
    pub body: Vec<Literal<T>>,
}

impl<T> ChoiceRule<T> {
    pub fn new(head: Aggregate<T>, body: impl IntoIterator<Item = Literal<T>>) -> Self {
        Self {
            head,
            body: body.into_iter().collect(),
        }
    }
}

impl<T> fmt::Display for ChoiceRule<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.body.is_empty() {
            self.head.fmt(f)
        } else {
            f.write_fmt(format_args!(
                "{} if {}",
                self.head,
                self.body
                    .iter()
                    .map(|b| b.to_string())
                    .collect::<Vec<_>>()
                    .join(" and ")
            ))
        }
    }
}

/// Rules generally have a disjunctive head and a conjunctive body,
/// but at this level we'll just collect vectors.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Rule<T> {
    pub head: Vec<Literal<T>>,
    pub body: Vec<Literal<T>>,
}

impl<T> Rule<T> {
    pub fn new(
        head: impl IntoIterator<Item = Literal<T>>,
        body: impl IntoIterator<Item = Literal<T>>,
    ) -> Self {
        Self {
            head: head.into_iter().collect(),
            body: body.into_iter().collect(),
        }
    }
}

impl<T> fmt::Display for Rule<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let head = || -> String {
            self.head
                .iter()
                .map(|h| h.to_string())
                .collect::<Vec<_>>()
                .join(" or ")
        };
        let body = || -> String {
            self.body
                .iter()
                .map(|b| b.to_string())
                .collect::<Vec<_>>()
                .join(" and ")
        };
        match (self.head.is_empty(), self.body.is_empty()) {
            (true, true) => Ok(()),
            (true, false) => f.write_fmt(format_args!("if {}", body())),
            (false, true) => f.write_fmt(format_args!("{}", head())),
            (false, false) => f.write_fmt(format_args!("{} if {}", head(), body())),
        }
    }
}

/// Render Minuet syntax as Rust tokens.
/// See the `minuet!` proc macro parser.
#[cfg(feature = "to-rust")]
mod to_rust {
    use proc_macro2::TokenStream;
    use quote::{quote, ToTokens};

    use super::*;

    impl ToTokens for Symbol {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            let name = self.name();
            tokens.extend(quote!(::minuet_syntax::Symbol::from(#name)));
        }
    }

    impl ToTokens for Constant {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.extend(match self {
                Constant::Name(n) => quote!(::minuet_syntax::Constant::Name(#n)),
                Constant::Number(i) => quote!(::minuet_syntax::Constant::Number(#i)),
            });
        }
    }

    impl ToTokens for Pool<Term> {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.extend(match self {
                Pool::Interval(l, u) => quote!(::minuet_syntax::Pool::interval(#l, #u)),
                Pool::Set(s) => quote!(::minuet_syntax::Pool::set([#(#s),*])),
            });
        }
    }

    impl ToTokens for RelOp {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.extend(match self {
                RelOp::Eq => quote!(::minuet_syntax::RelOp::Eq),
                RelOp::Ne => quote!(::minuet_syntax::RelOp::Ne),
                RelOp::Lt => quote!(::minuet_syntax::RelOp::Lt),
                RelOp::Gt => quote!(::minuet_syntax::RelOp::Gt),
                RelOp::Leq => quote!(::minuet_syntax::RelOp::Leq),
                RelOp::Geq => quote!(::minuet_syntax::RelOp::Geq),
            });
        }
    }

    impl ToTokens for UnaryOp {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.extend(match self {
                UnaryOp::Abs => quote!(::minuet_syntax::UnaryOp::Abs),
                UnaryOp::Neg => quote!(::minuet_syntax::UnaryOp::Neg),
                UnaryOp::Not => quote!(::minuet_syntax::UnaryOp::Not),
            });
        }
    }

    impl ToTokens for BinOp {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.extend(match self {
                BinOp::Add => quote!(::minuet_syntax::BinOp::Add),
                BinOp::Sub => quote!(::minuet_syntax::BinOp::Sub),
                BinOp::Mul => quote!(::minuet_syntax::BinOp::Mul),
                BinOp::Exp => quote!(::minuet_syntax::BinOp::Exp),
                BinOp::Div => quote!(::minuet_syntax::BinOp::Div),
                BinOp::Rem => quote!(::minuet_syntax::BinOp::Rem),
            });
        }
    }

    impl ToTokens for Term {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.extend(match self {
                Term::Constant(c) => quote!(::minuet_syntax::Term::Constant(#c)),
                Term::Variable(v) => quote!(::minuet_syntax::Term::Variable(#v)),
                Term::Pool(p) => quote!(::minuet_syntax::Term::Pool(#p)),
                Term::UnaryOperation(op, t) => {
                    quote!(::minuet_syntax::Term::unary_operation(#op, #t))
                }
                Term::BinaryOperation(l, op, r) => {
                    quote!(::minuet_syntax::Term::binary_operation(#l, #op, #r))
                }
            })
        }
    }

    impl ToTokens for Application<Term> {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            let predicate = &self.predicate;
            let arguments = &self.arguments;
            tokens.extend(quote!(::minuet_syntax::Application::new(#predicate, [#(#arguments),*])));
        }
    }

    impl ToTokens for Atom<Term> {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.extend(match self {
                Atom::Aux(_) => unimplemented!("auxiliary"),
                Atom::Agg(agg) => todo!("aggregate {agg:?}"),
                Atom::App(app) => quote!(Atom::App(#app)),
            })
        }
    }

    impl ToTokens for AggregateBounds<Term> {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            let lb = &self.lower_bound;
            let ub = &self.upper_bound;
            tokens.extend(quote!(::minuet_syntax::AggregateBounds::new(#lb, #ub)));
        }
    }

    impl ToTokens for Aggregate<Term> {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            let choices = &self.choices;
            tokens.extend(if let Some(bounds) = &self.bounds {
                quote!(::minuet_syntax::Aggregate::new([#(#choices),*], Some(#bounds)))
            } else {
                quote!(::minuet_syntax::Aggregate::new([#(#choices),*], None))
            });
        }
    }

    impl ToTokens for Literal<Term> {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.extend(match self {
                Literal::Positive(atom) => {
                    quote!(::minuet_syntax::Literal::Positive(#atom))
                }
                Literal::Negative(atom) => {
                    quote!(::minuet_syntax::Literal::Negative(#atom))
                }
                Literal::DoubleNegative(atom) => {
                    quote!(::minuet_syntax::Literal::DoubleNegative(#atom))
                }
                Literal::Relation(left, op, right) => {
                    quote!(::minuet_syntax::Literal::relation(#left, #op, #right))
                }
            });
        }
    }

    impl ToTokens for Rule<Term> {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            let head = &self.head;
            let body = &self.body;
            tokens.extend(quote!(::minuet_syntax::Rule::new([#(#head),*], [#(#body),*])));
        }
    }

    impl ToTokens for ChoiceRule<Term> {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            let head = &self.head;
            let body = &self.body;
            tokens.extend(quote!(::minuet_syntax::ChoiceRule::new(#head, [#(#body),*])));
        }
    }

    impl ToTokens for BaseRule<Term> {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.extend(match self {
                BaseRule::Choice(rule) => {
                    quote!(::minuet_syntax::BaseRule::Choice(#rule))
                }
                BaseRule::Disjunctive(rule) => {
                    quote!(::minuet_syntax::BaseRule::Disjunctive(#rule))
                }
            })
        }
    }
}

/// These constructor macros can make tests involving syntactic elements
/// (most of them) much more readable. They are *not* intended as a public
/// interface, and *should* be behind `#[cfg(test)]`, but [cargo can't
/// currently export test code across crates](https://github.com/rust-lang/cargo/issues/8379).
#[cfg(feature = "macros")]
mod macros {
    #[macro_export]
    macro_rules! sym {
        ($name: ident) => {
            Symbol::from(stringify!($name))
        };
    }

    #[macro_export]
    macro_rules! atom {
        ({$($lit: expr),*}) => {
            Atom::Agg(Aggregate::new([$($lit),*], None))
        };
        ($pred: ident) => {
            Atom::App(Application::new(sym!($pred), []))
        };
        ($pred: ident($($arg: expr),*)) => {
            Atom::App(Application::new(sym!($pred), [$($arg.into()),*]))
        };
    }

    #[macro_export]
    macro_rules! pos {
        ($pred: ident $(($($args: tt)*))?) => {
            Literal::Positive(atom!($pred$(($($args)*))?))
        };
        ($lit: expr) => {
            Literal::Positive($lit)
        };
    }

    #[macro_export]
    macro_rules! neg {
        ($pred: ident $(($($args: tt)*))?) => {
            Literal::Negative(atom!($pred$(($($args)*))?))
        };
        ($lit: expr) => {
            Literal::Negative($lit)
        };
    }

    #[macro_export]
    macro_rules! nneg {
        ($pred: ident $(($($args: tt)*))?) => {
            Literal::DoubleNegative(atom!($pred$(($($args)*))?))
        };
        ($lit: expr) => {
            Literal::DoubleNegative($lit)
        };
    }

    #[macro_export]
    macro_rules! rel {
        ($l: expr, $op: ident, $r: expr) => {
            Literal::relation($l.into(), RelOp::$op, $r.into())
        };
    }

    #[macro_export]
    macro_rules! constant {
        ($c: literal) => {
            Term::Constant($c.into())
        };
    }
    #[macro_export]
    macro_rules! var {
        ($name: ident) => {
            Term::Variable(sym!($name))
        };
    }

    #[macro_export]
    macro_rules! pool {
        ({$($elt: expr),*}) => {
            Pool::set([$($elt.into()),*])
        };
        ($start: literal .. $end: literal) => {
            Pool::interval(constant!($start), constant!($end))
        };
        ($start: expr => $end: expr) => {
            Pool::interval($start, $end)
        };
    }

    #[macro_export]
    macro_rules! unary {
        ($op: ident, $e: expr) => {
            Term::unary_operation(UnaryOp::$op, $e.into())
        };
    }

    #[macro_export]
    macro_rules! binary {
        ($l: expr, $op: ident, $r: expr) => {
            Term::binary_operation($l.into(), BinOp::$op, $r.into())
        };
    }

    #[macro_export]
    macro_rules! rule {
        ({$($choice: expr),* $(,)?}) => {{
            let agg = Aggregate::new([$($choice),*], None);
            BaseRule::<Term>::Choice(ChoiceRule::new(agg, []))
        }};
        ($lb: literal {$($choice: expr),* $(,)?} $ub: literal) => {{
            let bnd = AggregateBounds::new($lb.into(), $ub.into());
            let agg = Aggregate::new([$($choice),*], Some(bnd));
            BaseRule::<Term>::Choice(ChoiceRule::new(agg, []))
        }};
        ([$($head: expr),* $(,)?]) => {
            BaseRule::<Term>::Disjunctive(Rule::new([$($head),*], []))
        };
        ([$($head: expr),* $(,)?], [$($body: expr),* $(,)?]) => {
            BaseRule::<Term>::Disjunctive(Rule::new([$($head),*], [$($body),*]))
        };
    }
}
