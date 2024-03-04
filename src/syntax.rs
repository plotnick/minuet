//! Syntactic elements of a simple ASP-like logic language.
//!
//! See "Abstract Gringo" (2015) by Gebser, et al. and the
//! "ASP-Core-2 Input Language Format" (2012). A string or
//! macro parser may layer whatever surface syntax it likes
//! on top of these elements; see the example in the `test`
//! module.

#![allow(dead_code)]

use std::collections::BTreeSet;
use std::fmt;

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
/// and logical (i.e., classical, strong) negation.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum UnaryOp {
    Abs,
    Neg,
    Not,
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
    Choice(Pool<Term>),
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

impl From<Constant> for Term {
    fn from(c: Constant) -> Self {
        Self::Constant(c)
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Term::*;
        use UnaryOp::*;
        match self {
            Constant(x) => x.fmt(f),
            Variable(x) => x.fmt(f),
            Choice(x) => x.fmt(f),
            UnaryOperation(Abs, x) => f.write_fmt(format_args!("|{x}|")),
            UnaryOperation(Neg, x) => f.write_fmt(format_args!("-{x}")),
            UnaryOperation(Not, x) => f.write_fmt(format_args!("~{x}")),
            BinaryOperation(x, op, y) => f.write_fmt(format_args!("{x} {op} {y}")),
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

/// An _aggregate atom_ represents all possible subsets of some set of values.
/// TODO: Cardinality bounds.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Aggregate<T> {
    pub choices: Vec<Literal<T>>,
}

impl<T> fmt::Display for Aggregate<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!(
            "{{{}}}",
            self.choices
                .iter()
                .map(|l| l.to_string())
                .collect::<Vec<_>>()
                .join(" or ")
        ))
    }
}

/// An _n_-ary predicate applied to a tuple of terms.
/// If _n_ = 0, the arguments are usually elided.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Application<T> {
    pub predicate: Symbol,
    pub arguments: Vec<T>,
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

    pub fn agg(atoms: impl IntoIterator<Item = Literal<T>>) -> Self {
        Self::Agg(Aggregate {
            choices: atoms.into_iter().collect(),
        })
    }

    pub fn app(predicate: Symbol, arguments: impl IntoIterator<Item = T>) -> Self {
        Self::App(Application {
            predicate,
            arguments: arguments.into_iter().collect(),
        })
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

#[cfg(test)]
#[macro_use]
pub(crate) mod test {
    use super::*;

    macro_rules! sym {
        [$s:ident] => {
            Symbol::new(String::from(stringify!($s)))
        };
    }

    #[test]
    fn symbol() {
        assert_eq!(sym![a], Symbol::new(String::from("a")));
        assert_eq!(sym![a], sym![a]);
        assert_ne!(sym![a], sym![b]);
    }

    macro_rules! constant {
        [($($c:tt)*)] => { constant![$($c)*] };
        [$s:ident] => { Constant::Name(sym![$s]) };
        [$i:literal] => { Constant::Number($i) };
        [-$i:literal] => { Constant::Number(-$i) };
    }

    #[test]
    fn constant() {
        assert_eq!(constant![a], Constant::Name(sym![a]));
        assert_eq!(constant![0], Constant::Number(0));
        assert_eq!(constant![a], "a".into());
        assert_eq!(constant![0], 0.into());
        assert_eq!(constant![-1], (-1).into());
        assert_ne!(constant![-1], 1.into());
    }

    macro_rules! term {
        [($($term:tt)*)] => { term![$($term)*] };
        [|($($term:tt)*)|] => { Term::unary_operation(UnaryOp::Abs, term![$($term)*]) };
        [|$a:tt|] => { Term::unary_operation(UnaryOp::Abs, term![$a]) };
        [-$a:literal] => { Term::Constant(Constant::Number(-$a)) };
        [-$a:tt] => { Term::unary_operation(UnaryOp::Neg, term![$a]) };
        [~$a:tt] => { Term::unary_operation(UnaryOp::Not, term![$a]) };
        [$a:tt + $b:tt] => { Term::binary_operation(term![$a], BinOp::Add, term![$b]) };
        [$a:tt - $b:tt] => { Term::binary_operation(term![$a], BinOp::Sub, term![$b]) };
        [$a:tt * $b:tt] => { Term::binary_operation(term![$a], BinOp::Mul, term![$b]) };
        [$a:tt ^ $b:tt] => { Term::binary_operation(term![$a], BinOp::Exp, term![$b]) };
        [$a:tt / $b:tt] => { Term::binary_operation(term![$a], BinOp::Div, term![$b]) };
        [$a:tt % $b:tt] => { Term::binary_operation(term![$a], BinOp::Rem, term![$b]) };
        [$a:tt $(or $b:tt)+] => { Term::Choice(Pool::set([term![$a], $(term![$b]),+])) };
        [$i:tt..$j:tt] => { Term::Choice(Pool::interval(term![$i], term![$j])) };
        [$a:literal] => { Term::Constant(Constant::Number($a)) };
        [$s:ident] => {
            // Prolog/ASP surface syntax: names of constants start with a lowercase
            // letter, and the names of variables start with an uppercase letter or
            // underscore.
            if stringify!($s).chars().take(1).all(char::is_lowercase) {
                Term::Constant(constant![$s])
            } else {
                Term::Variable(sym![$s])
            }
        };
    }

    #[test]
    fn term() {
        assert_eq!(
            term![a],
            Term::Constant(Constant::Name(Symbol::new(String::from("a"))))
        );
        assert_eq!(term![X], Term::Variable(Symbol::new(String::from("X"))));
        assert_eq!(term![1], Term::Constant(Constant::Number(1)));
        assert_eq!(term![-1], Term::Constant(Constant::Number(-1)));
        assert_eq!(term![-X], Term::unary_operation(UnaryOp::Neg, term![X]));
        assert_eq!(
            term![|(-3)|],
            Term::unary_operation(UnaryOp::Abs, term![-3])
        );
        assert_eq!(
            term![1..3],
            Term::Choice(Pool::interval(term![1], term![3]))
        );
        assert_eq!(
            term![1..N],
            Term::Choice(Pool::interval(term![1], term![N]))
        );
        assert_eq!(
            term![1 or 2 or 3],
            Term::Choice(Pool::set([term![1], term![2], term![3]]))
        );
        assert_eq!(
            term![1 + 2],
            Term::binary_operation(term![1], BinOp::Add, term![2])
        );
    }

    macro_rules! atom {
        // We need a little tt-muncher to delimit arguments.
        // This may be problematic as the term syntax grows.
        [@args [] [] -> [$($args:tt)*]] => {{
            let mut v = vec![$($args)*]; v.reverse(); v
        }};
        [@args [] [$($partial:tt)*] -> [$($args:tt)*]] => {
            atom![@args [] [] -> [term![$($partial)*], $($args)*]]
        };
        [@args [, $($rest:tt)*] [] -> [$($args:tt)*]] => {
            atom![@args [$($rest)*] [] -> [$($args)*]]
        };
        [@args [, $($rest:tt)*] [$($partial:tt)+] -> [$($args:tt)*]] => {
            atom![@args [$($rest)*] [] -> [term![$($partial)+], $($args)*]]
        };
        [@args [.. $j:literal $($rest:tt)*] [$i:literal $($partial:tt)*] -> [$($args:tt)*]] => {
            atom![@args [$($rest)*] [$($partial)*] -> [term![$i..$j], $($args)*]]
        };
        [@args [($($term:tt)*) $($rest:tt)*] [$($partial:tt)*] -> [$($args:tt)*]] => {
            atom![@args [$($rest)*] [$($partial)*] -> [term![($($term)*)], $($args)*]]
        };
        [@args [$pred:ident $($rest:tt)*] [$($partial:tt)*] -> [$($args:tt)*]] => {
            atom![@args [$($rest)*] [$pred $($partial)*] -> [$($args)*]]
        };
        [@args [$i:literal $($rest:tt)*] [$($partial:tt)*] -> [$($args:tt)*]] => {
            atom![@args [$($rest)*] [$i $($partial)*] -> [$($args)*]]
        };

        // And another to delimit disjuncts in choice rules.
        // It would be nice if this could share code with lit!
        [@agg [] [] -> [$($agg:tt)*]] => {{
            let mut v = vec![$($agg)*]; v.reverse(); v
        }};
        [@agg [] [$($partial:tt)*] -> [$($agg:tt)*]] => {
            atom![@agg [] [] -> [Literal::Positive(atom![$($partial)*]), $($agg)*]]
        };
        [@agg [not not $($rest:tt)*] [] -> [$($agg:tt)*]] => {
            atom![@agg [$($rest)*] [not not] -> [$($agg)*]]
        };
        [@agg [not $($rest:tt)*] [] -> [$($agg:tt)*]] => {
            atom![@agg [$($rest)*] [not] -> [$($agg)*]]
        };
        [@agg [or $($rest:tt)*] [] -> [$($agg:tt)*]] => {
            atom![@agg [$($rest)*] [] -> [$($agg)*]]
        };
        [@agg [or $($rest:tt)*] [not not $($partial:tt)*] -> [$($agg:tt)*]] => {
            atom![@agg [$($rest)*] [] -> [Literal::DoubleNegative(atom![$($partial)*]), $($agg)*]]
        };
        [@agg [or $($rest:tt)*] [not $($partial:tt)*] -> [$($agg:tt)*]] => {
            atom![@agg [$($rest)*] [] -> [Literal::Negative(atom![$($partial)*]), $($agg)*]]
        };
        [@agg [or $($rest:tt)*] [$($partial:tt)*] -> [$($agg:tt)*]] => {
            atom![@agg [$($rest)*] [] -> [Literal::Positive(atom![$($partial)*]), $($agg)*]]
        };
        [@agg [$pred:ident($($args:tt)*) $($rest:tt)*] [not not] -> [$($agg:tt)*]] => {
            atom![@agg [$($rest)*] [] -> [Literal::DoubleNegative(atom![$pred($($args)*)]), $($agg)*]]
        };
        [@agg [$pred:ident $($rest:tt)*] [not not] -> [$($agg:tt)*]] => {
            atom![@agg [$($rest)*] [not not $pred] -> [$($agg)*]]
        };
        [@agg [$pred:ident($($args:tt)*) $($rest:tt)*] [not] -> [$($agg:tt)*]] => {
            atom![@agg [$($rest)*] [not $pred($($args)*)] -> [$($agg)*]]
        };
        [@agg [$pred:ident $($rest:tt)*] [not] -> [$($agg:tt)*]] => {
            atom![@agg [$($rest)*] [not $pred] -> [$($agg)*]]
        };
        [@agg [$pred:ident($($args:tt)*) $($rest:tt)*] [] -> [$($agg:tt)*]] => {
            atom![@agg [$($rest)*] [$pred($($args)*)] -> [$($agg)*]]
        };
        [@agg [$pred:ident $($rest:tt)*] [] -> [$($agg:tt)*]] => {
            atom![@agg [$($rest)*] [$pred] -> [$($agg)*]]
        };

        [{$($agg:tt)*}] => { Atom::<Term>::agg(atom![@agg [$($agg)*] [] -> []]) };
        [$pred:ident($($args:tt)*)] => { Atom::<Term>::app(sym![$pred], atom![@args [$($args)*] [] -> []]) };
        [$pred:ident] => { Atom::<Term>::app(sym![$pred], vec![]) };
    }

    #[test]
    fn atom() {
        assert_eq!(atom![f], Atom::<Term>::app(sym![f], vec![]));
        assert_eq!(atom![f()], Atom::<Term>::app(sym![f], vec![]));
        assert_eq!(atom![f(a)], Atom::<Term>::app(sym![f], vec![term![a]]));
        assert_eq!(
            atom![f(a, b)],
            Atom::<Term>::app(sym![f], vec![term![a], term![b]])
        );
        assert_eq!(
            atom![f(a or b)],
            Atom::<Term>::app(sym![f], vec![term![a or b]])
        );
        assert_eq!(
            atom![f(0 or 1)],
            Atom::<Term>::app(sym![f], vec![term![0 or 1]])
        );
        assert_eq!(
            atom![f(a or b, 0 or 1)],
            Atom::<Term>::app(sym![f], vec![term![a or b], term![0 or 1]])
        );
        assert_eq!(
            atom![f(0..1)],
            Atom::<Term>::app(sym![f], vec![term![0..1]])
        );
        assert_eq!(
            atom![f(X, Y)],
            Atom::<Term>::app(sym![f], vec![term![X], term![Y]])
        );
        assert_eq!(
            atom![{ p }],
            Atom::<Term>::agg([Literal::Positive(atom![p]),]),
        );
        assert_eq!(
            atom![{f(a) or f(b)}],
            Atom::<Term>::agg([
                Literal::Positive(atom![f(a)]),
                Literal::Positive(atom![f(b)])
            ]),
        );
        assert_eq!(
            atom![{f(a) or not f(b) or not not f(c)}],
            Atom::<Term>::agg([
                Literal::Positive(atom![f(a)]),
                Literal::Negative(atom![f(b)]),
                Literal::DoubleNegative(atom![f(c)])
            ]),
        );
    }

    macro_rules! lit {
        [($($lit:tt)*)] => { lit![$($lit)*] };
        [{$($atom:tt)*}] => { Literal::Positive(atom![{$($atom)*}]) };
        [$x:tt = $y:tt] => { Literal::relation(term![$x], RelOp::Eq, term![$y]) };
        [$x:tt != $y:tt] => { Literal::relation(term![$x], RelOp::Ne, term![$y]) };
        [$x:tt < $y:tt] => { Literal::relation(term![$x], RelOp::Lt, term![$y]) };
        [$x:tt > $y:tt] => { Literal::relation(term![$x], RelOp::Gt, term![$y]) };
        [$x:tt <= $y:tt] => { Literal::relation(term![$x], RelOp::Leq, term![$y]) };
        [$x:tt >= $y:tt] => { Literal::relation(term![$x], RelOp::Geq, term![$y]) };
        [not not $pred:ident($($arg:tt)*)] => { Literal::DoubleNegative(atom![$pred($($arg)*)]) };
        [not not $pred:ident] => { Literal::DoubleNegative(atom![$pred]) };
        [not $pred:ident($($arg:tt)*)] => { Literal::Negative(atom![$pred($($arg)*)]) };
        [not $pred:ident] => { Literal::Negative(atom![$pred]) };
        [$pred:ident($($arg:tt)*)] => { Literal::Positive(atom![$pred($($arg)*)]) };
        [$pred:ident] => { Literal::Positive(atom![$pred]) };
    }

    #[test]
    fn literal() {
        use Literal::*;
        assert_eq!(lit![p], Positive::<Term>(atom![p]));
        assert_eq!(lit![p(a, b)], Positive::<Term>(atom![p(a, b)]));
        assert_eq!(lit![not p(a, b)], Negative::<Term>(atom![p(a, b)]));
        assert_eq!(
            lit![not not p(a, b)],
            DoubleNegative::<Term>(atom![p(a, b)])
        );
    }

    #[test]
    fn relation() {
        use RelOp::*;
        let rel = Literal::relation;
        assert_eq!(lit![0 = 1], rel(term![0], Eq, term![1]));
        assert_eq!(lit![0 < 1], rel(term![0], Lt, term![1]));
        assert_eq!(lit![0 > 1], rel(term![0], Gt, term![1]));
        assert_eq!(lit![0 <= 1], rel(term![0], Leq, term![1]));
        assert_eq!(lit![0 >= 1], rel(term![0], Geq, term![1]));
    }

    /// An auxiliary macro with "internal" tt-munching rules of the form:
    /// `[@internal [unprocessed] -> [accumulator] [carry]] => { ... }`.
    /// We need the auxiliary so we don't infinitely recurse matching `[$($rest)*]`.
    macro_rules! rule_aux {
        // Common literal muncher: $next will be @head or @body.
        [@lit @$next:ident [($($lit:tt)*) $($rest:tt)*] -> [$($acc:tt)*] [$($carry:tt)*]] => {
            rule_aux![@$next [$($rest)*] -> [lit![($($lit)*)], $($acc)*] [$($carry)*]]
        };
        [@lit @$next:ident [$x:tt = $y:tt $($rest:tt)*] -> [$($acc:tt)*] [$($carry:tt)*]] => {
            rule_aux![@$next [$($rest)*] -> [lit![$x = $y], $($acc)*] [$($carry)*]]
        };
        [@lit @$next:ident [$x:tt != $y:tt $($rest:tt)*] -> [$($acc:tt)*] [$($carry:tt)*]] => {
            rule_aux![@$next [$($rest)*] -> [lit![$x != $y], $($acc)*] [$($carry)*]]
        };
        [@lit @$next:ident [$x:tt < $y:tt $($rest:tt)*] -> [$($acc:tt)*] [$($carry:tt)*]] => {
            rule_aux![@$next [$($rest)*] -> [lit![$x < $y], $($acc)*] [$($carry)*]]
        };
        [@lit @$next:ident [$x:tt > $y:tt $($rest:tt)*] -> [$($acc:tt)*] [$($carry:tt)*]] => {
            rule_aux![@$next [$($rest)*] -> [lit![$x > $y], $($acc)*] [$($carry)*]]
        };
        [@lit @$next:ident [$x:tt <= $y:tt $($rest:tt)*] -> [$($acc:tt)*] [$($carry:tt)*]] => {
            rule_aux![@$next [$($rest)*] -> [lit![$x <= $y], $($acc)*] [$($carry)*]]
        };
        [@lit @$next:ident [$x:tt >= $y:tt $($rest:tt)*] -> [$($acc:tt)*] [$($carry:tt)*]] => {
            rule_aux![@$next [$($rest)*] -> [lit![$x >= $y], $($acc)*] [$($carry)*]]
        };
        [@lit @$next:ident [not not $pred:ident($($args:tt)*) $($rest:tt)*] -> [$($acc:tt)*] [$($carry:tt)*]] => {
            rule_aux![@$next [$($rest)*] -> [lit![not not $pred($($args)*)], $($acc)*] [$($carry)*]]
        };
        [@lit @$next:ident [not not $pred:ident $($rest:tt)*] -> [$($acc:tt)*] [$($carry:tt)*]] => {
            rule_aux![@$next [$($rest)*] -> [lit![not not $pred], $($acc)*] [$($carry)*]]
        };
        [@lit @$next:ident [not $pred:ident($($args:tt)*) $($rest:tt)*] -> [$($acc:tt)*] [$($carry:tt)*]] => {
            rule_aux![@$next [$($rest)*] -> [lit![not $pred($($args)*)], $($acc)*] [$($carry)*]]
        };
        [@lit @$next:ident [not $pred:ident $($rest:tt)*] -> [$($acc:tt)*] [$($carry:tt)*]] => {
            rule_aux![@$next [$($rest)*] -> [lit![not $pred], $($acc)*] [$($carry)*]]
        };
        [@lit @$next:ident [$pred:ident($($args:tt)*) $($rest:tt)*] -> [$($acc:tt)*] [$($carry:tt)*]] => {
            rule_aux![@$next [$($rest)*] -> [lit![$pred($($args)*)], $($acc)*] [$($carry)*]]
        };
        [@lit @$next:ident [$pred:ident $($rest:tt)*] -> [$($acc:tt)*] [$($carry:tt)*]] => {
            rule_aux![@$next [$($rest)*] -> [lit![$pred], $($acc)*] [$($carry)*]]
        };
        [@lit @$next:ident [$($rest:tt)*] -> [$($acc:tt)*] [$($carry:tt)*]] => {
            rule_aux![@$next [$($rest)*] -> [$($acc)*] [$($carry)*]]
        };

        // Head base cases: no more tokens in the head, punt to the body muncher.
        [@head [] -> [$($head:tt)*] []] => {
            rule_aux![@body [] -> [] [$($head)*]]
        };
        [@head [if $($body:tt)*] -> [$($head:tt)*] []] => {
            rule_aux![@body [$($body)*] -> [] [$($head)*]]
        };

        // Accumulate disjunction of head literals.
        [@head [and $($rest:tt)*] -> [$($head:tt)*] []] => {
            compile_error!("only disjunctions allowed in rule heads")
        };
        [@head [or $($rest:tt)*] -> [$($head:tt)*] []] => {
            rule_aux![@lit @head [$($rest)*] -> [$($head)*] []]
        };
        [@head [$($rest:tt)*] -> [$($head:tt)*] []] => {
            rule_aux![@lit @head [$($rest)*] -> [$($head)*] []]
        };

        // Choice rules have a single aggregate atom as head.
        [@choice [{$($choice:tt)*} if $($body:tt)*] -> [] []] => {
            rule_aux![@body [$($body)*] -> [] [{$($choice)*}]]
        };
        [@choice [{$($choice:tt)*}] -> [] []] => {
            rule_aux![@body [] -> [] [{$($choice)*}]]
        };

        // Choice rule body base case.
        [@body [] -> [$($body:tt)*] [{$($choice:tt)*}]] => {{
            let head = match atom![{$($choice)*}] {
                Atom::Agg(agg) => agg,
                _ => unimplemented!("invalid choice rule"),
            };
            let mut body = vec![$($body)*]; body.reverse();
            BaseRule::Choice(ChoiceRule::new(head, body))
        }};

        // Disjunctive rule body base case.
        [@body [] -> [$($body:tt)*] [$($head:tt)*]] => {{
            let mut head = vec![$($head)*]; head.reverse();
            let mut body = vec![$($body)*]; body.reverse();
            BaseRule::Disjunctive(Rule::new(head, body))
        }};

        // Accumulate conjunction of body literals and carry the head.
        [@body [and $($rest:tt)*] -> [$($body:tt)*] [$($head:tt)*]] => {
            rule_aux![@lit @body [$($rest)*] -> [$($body)*] [$($head)*]]
        };
        [@body [or $($rest:tt)*] -> [$($body:tt)*] [$($head:tt)*]] => {
            compile_error!("only conjunctions allowed in rule bodies")
        };
        [@body [if $($rest:tt)*] -> [$($body:tt)*] [$($head:tt)*]] => {
            compile_error!("only one body allowed per rule")
        };
        [@body [$($rest:tt)*] -> [$($body:tt)*] [$($head:tt)*]] => {
            rule_aux![@lit @body [$($rest)*] -> [$($body)*] [$($head)*]]
        };
    }

    macro_rules! rule {
        // Top level: punt to auxiliary macro.
        [{$($choice:tt)*} if $($body:tt)*] => { rule_aux![@choice [{$($choice)*} if $($body)*] -> [] []] };
        [{$($choice:tt)*}] => { rule_aux![@choice [{$($choice)*}] -> [] []] };
        [if $($body:tt)*] => { rule_aux![@body [$($body)*] -> [] []] };
        [$($rest:tt)*] => { rule_aux![@head [$($rest)*] -> [] []] };
    }

    // Ground variants.
    macro_rules! gatom {
        [$($x:tt)*] => { atom![$($x)*].ground() };
    }

    macro_rules! glit {
        [$($lit:tt)*] => { lit![$($lit)*].ground() };
    }

    #[test]
    fn rule() {
        // Heads with no bodies are (disjunctive) "facts".
        assert_eq!(
            rule![p],
            BaseRule::Disjunctive(Rule::<Term>::new([lit![p]], []))
        );
        assert_eq!(
            rule![p(a)],
            BaseRule::Disjunctive(Rule::new([lit![p(a)]], []))
        );
        assert_eq!(
            rule![p(a or b)],
            BaseRule::Disjunctive(Rule::new([lit![p(a or b)]], []))
        );
        assert_eq!(
            rule![p(a) or p(b)],
            BaseRule::Disjunctive(Rule::new([lit![p(a)], lit![p(b)]], []))
        );
        assert_eq!(
            rule![0 = 1],
            BaseRule::Disjunctive(Rule::new([lit![0 = 1]], []))
        );
        assert_eq!(
            rule![0 != (0 + 1)],
            BaseRule::Disjunctive(Rule::new([lit![0 != (0 + 1)]], []))
        );
        assert_eq!(
            rule![0 < 1],
            BaseRule::Disjunctive(Rule::new([lit![0 < 1]], []))
        );
        assert_eq!(
            rule![0 >= 1 if 1 < 0],
            BaseRule::Disjunctive(Rule::new([lit![0 >= 1]], [lit![1 < 0]]))
        );

        // Look, Ma, negations in the head! Why, it's the excluded middle!
        assert_eq!(
            rule![p or not p],
            BaseRule::Disjunctive(Rule::<Term>::new([lit![p], lit![not p]], []))
        );

        // Choice rules may be viewed as syntactic sugar for such negations.
        assert_eq!(
            rule![{ p }],
            BaseRule::Choice(ChoiceRule::new(
                Aggregate {
                    choices: vec![lit![p]]
                },
                []
            ))
        );

        // Bodies without heads are (conjunctive) "constraints".
        assert_eq!(
            rule![if q(a)],
            BaseRule::Disjunctive(Rule::new([], [lit![q(a)]]))
        );
        assert_eq!(
            rule![if q(a) and q(b) and q(c)],
            BaseRule::Disjunctive(Rule::new([], [lit![q(a)], lit![q(b)], lit![q(c)]]))
        );

        // Rules generally have a (disjunctive) head and a (conjunctive) body.
        assert_eq!(
            rule![p if q],
            BaseRule::Disjunctive(Rule::<Term>::new([lit![p]], [lit![q]]))
        );
        assert_eq!(
            rule![p(a) or p(b) or p(c) if q(a) and q(b) and q(c)],
            BaseRule::Disjunctive(Rule::new(
                [lit![p(a)], lit![p(b)], lit![p(c)]],
                [lit![q(a)], lit![q(b)], lit![q(c)]]
            ))
        );
        assert_eq!(
            rule![p(a, b) if q(a) and not q(b)],
            BaseRule::Disjunctive(Rule::new([lit![p(a, b)]], [lit![q(a)], lit![not q(b)]]))
        );
        assert_eq!(
            rule![p(a, b) if not q(a) and q(b)],
            BaseRule::Disjunctive(Rule::new([lit![p(a, b)]], [lit![not q(a)], lit![q(b)]]))
        );
        assert_eq!(
            rule![0 < 1 if 0 > 1],
            BaseRule::Disjunctive(Rule::new([lit![0 < 1]], [lit![0 > 1]]))
        );
    }
}
