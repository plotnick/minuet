//! Syntactic elements of a simple ASP-like logic language.
//!
//! See "Abstract Gringo" (2015) by Gebser, et al. and the
//! "ASP-Core-2 Input Language Format" (2012). A string or
//! macro parser may layer whatever surface syntax it likes
//! on top of these elements; see the example in [`test`].

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
        Self::Name(Symbol::new(String::from(s)))
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

/// Denotes an interval or arbitrary set of constants.
/// See the `image` module for operations on such sets.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Pool<T> {
    Interval(Box<T>, Box<T>),
    Set(BTreeSet<T>),
}

impl<T> Pool<T>
where
    T: Ord,
{
    pub fn empty() -> Self {
        Self::Set(BTreeSet::new())
    }

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

/// Ground (variable-free) element that represents a fixed set of values.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum GroundTerm {
    Constant(Constant),
    Choice(Pool<GroundTerm>),
    UnaryOperation(UnaryOp, Box<GroundTerm>),
    BinaryOperation(Box<GroundTerm>, BinOp, Box<GroundTerm>),
}

impl GroundTerm {
    /// Boxing constructor.
    pub fn unary_operation(op: UnaryOp, x: GroundTerm) -> Self {
        Self::UnaryOperation(op, Box::new(x))
    }

    /// Boxing constructor.
    pub fn binary_operation(x: GroundTerm, op: BinOp, y: GroundTerm) -> Self {
        Self::BinaryOperation(Box::new(x), op, Box::new(y))
    }
}

impl From<Constant> for GroundTerm {
    fn from(c: Constant) -> Self {
        Self::Constant(c)
    }
}

impl fmt::Display for GroundTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use GroundTerm::*;
        use UnaryOp::*;
        match self {
            Constant(x) => x.fmt(f),
            Choice(x) => x.fmt(f),
            UnaryOperation(Abs, x) => f.write_fmt(format_args!("|{x}|")),
            UnaryOperation(Neg, x) => f.write_fmt(format_args!("-{x}")),
            UnaryOperation(Not, x) => f.write_fmt(format_args!("~{x}")),
            BinaryOperation(x, op, y) => f.write_fmt(format_args!("{x} {op} {y}")),
        }
    }
}

/// An atomic formula is a predicate (_n_-ary relation) applied to
/// a tuple of terms. If _n_ = 0, we may elide the argument tuple.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Atom<T> {
    pub predicate: Symbol,
    pub arguments: Vec<T>,
}

impl<T> Atom<T> {
    pub fn new(predicate: Symbol, arguments: impl IntoIterator<Item = T>) -> Self {
        Self {
            predicate,
            arguments: arguments.into_iter().collect(),
        }
    }
}

impl<T> fmt::Display for Atom<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.arguments.is_empty() {
            self.predicate.fmt(f)
        } else {
            f.write_fmt(format_args!(
                "{}({})",
                self.predicate,
                self.arguments
                    .iter()
                    .map(|arg| arg.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ))
        }
    }
}

/// An atomic formula, its single or double negation as failure,
/// or a boolean arithmetic relation (e.g., `1 < 2`). (See Lifschitz,
/// "ASP" §5.8 on why triple negation is unnecessary.)
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
        matches!(self, Literal::Positive(..))
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

/// A rule has a disjunctive head and conjunctive body, either of
/// which may be empty. Literals in either may contain variables.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Rule {
    pub head: Vec<Literal<Term>>,
    pub body: Vec<Literal<Term>>,
}

impl Rule {
    pub fn new(head: Vec<Literal<Term>>, body: Vec<Literal<Term>>) -> Self {
        Self { head, body }
    }
}

impl fmt::Display for Rule {
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
    }

    macro_rules! constant {
        [$s:ident] => { Constant::Name(sym![$s]) };
        [$i:literal] => { Constant::Number($i) };
        [-$i:literal] => { Constant::Number(-$i) };
    }

    #[test]
    fn constant() {
        assert_eq!(constant![a], Constant::Name(sym![a]));
        assert_eq!(constant![0], Constant::Number(0));
    }

    macro_rules! term {
        [($($term:tt)*)] => { term![$($term)*] };
        [|($($term:tt)*)|] => { Term::unary_operation(UnaryOp::Abs, term![$($term)*]) };
        [|$a:tt|] => { Term::unary_operation(UnaryOp::Abs, term![$a]) };
        [- $a:tt] => { Term::unary_operation(UnaryOp::Neg, term![$a]) };
        [~ $a:tt] => { Term::unary_operation(UnaryOp::Not, term![$a]) };
        [$a:tt + $b:tt] => { Term::binary_operation(term![$a], BinOp::Add, term![$b]) };
        [$a:tt - $b:tt] => { Term::binary_operation(term![$a], BinOp::Sub, term![$b]) };
        [$a:tt * $b:tt] => { Term::binary_operation(term![$a], BinOp::Mul, term![$b]) };
        [$a:tt ^ $b:tt] => { Term::binary_operation(term![$a], BinOp::Exp, term![$b]) };
        [$a:tt / $b:tt] => { Term::binary_operation(term![$a], BinOp::Div, term![$b]) };
        [$a:tt % $b:tt] => { Term::binary_operation(term![$a], BinOp::Rem, term![$b]) };
        [$a:tt $(or $b:tt)+] => { Term::Choice(Pool::set([term![$a], $(term![$b]),+])) };
        [$i:tt..$j:tt] => { Term::Choice(Pool::interval(term![$i], term![$j])) };
        [$i:literal] => { Term::Constant(Constant::Number($i)) };
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
        assert_eq!(term![-1], Term::unary_operation(UnaryOp::Neg, term![1]));
        assert_eq!(
            term![|(-3)|],
            Term::unary_operation(UnaryOp::Abs, term![-3])
        );
        assert_eq!(
            term![1..3],
            Term::Choice(Pool::interval(term![1], term![3]))
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

        [$pred:ident($($args:tt)*)] => { Atom::new(sym![$pred], atom![@args [$($args)*] [] -> []]) };
        [$pred:ident] => { Atom::new(sym![$pred], vec![]) };
    }

    #[test]
    fn atom() {
        assert_eq!(atom![f], Atom::<Term>::new(sym![f], vec![]));
        assert_eq!(atom![f()], Atom::<Term>::new(sym![f], vec![]));
        assert_eq!(atom![f(a)], Atom::<Term>::new(sym![f], vec![term![a]]));
        assert_eq!(
            atom![f(a, b)],
            Atom::<Term>::new(sym![f], vec![term![a], term![b]])
        );
        assert_eq!(
            atom![f(a or b)],
            Atom::<Term>::new(sym![f], vec![term![a or b]])
        );
        assert_eq!(
            atom![f(0 or 1)],
            Atom::<Term>::new(sym![f], vec![term![0 or 1]])
        );
        assert_eq!(
            atom![f(a or b, 0 or 1)],
            Atom::<Term>::new(sym![f], vec![term![a or b], term![0 or 1]])
        );
        assert_eq!(
            atom![f(0..1)],
            Atom::<Term>::new(sym![f], vec![term![0..1]])
        );
        assert_eq!(
            atom![f(X, Y)],
            Atom::<Term>::new(sym![f], vec![term![X], term![Y]])
        );
    }

    macro_rules! lit {
        [($($lit:tt)*)] => { lit![$($lit)*] };
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
        [@head [if $($rest:tt)*] -> [$($head:tt)*] []] => {
            rule_aux![@body [$($rest)*] -> [] [$($head)*]]
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

        // Body base case: we've accumulated a whole rule.
        // Reverse the head & body and make an instance.
        [@body [] -> [$($body:tt)*] [$($head:tt)*]] => {{
            let mut head = vec![$($head)*]; head.reverse();
            let mut body = vec![$($body)*]; body.reverse();
            Rule::new(head, body)
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
        [if $($body:tt)*] => { rule_aux![@body [$($body)*] -> [] []] };
        [$($rest:tt)*] => { rule_aux![@head [$($rest)*] -> [] []] };
    }

    #[test]
    fn rule() {
        // Heads with no bodies are (disjunctive) "facts".
        assert_eq!(rule![p], Rule::new(vec![lit![p]], vec![]));
        assert_eq!(rule![p(a)], Rule::new(vec![lit![p(a)]], vec![]));
        assert_eq!(rule![p(a or b)], Rule::new(vec![lit![p(a or b)]], vec![]));
        assert_eq!(
            rule![p(a) or p(b)],
            Rule::new(vec![lit![p(a)], lit![p(b)]], vec![])
        );
        assert_eq!(rule![0 = 1], Rule::new(vec![lit![0 = 1]], vec![]));
        assert_eq!(
            rule![0 != (0 + 1)],
            Rule::new(vec![lit![0 != (0 + 1)]], vec![])
        );
        assert_eq!(rule![0 < 1], Rule::new(vec![lit![0 < 1]], vec![]));
        assert_eq!(
            rule![0 >= 1 if 1 < 0],
            Rule::new(vec![lit![0 >= 1]], vec![lit![1 < 0]])
        );

        // Look, Ma, negations in the head! Why, it's the excluded middle!
        assert_eq!(
            rule![p or not p],
            Rule::new(vec![lit![p], lit![not p]], vec![])
        );

        // Bodies without heads are (conjunctive) "constraints".
        assert_eq!(rule![if q(a)], Rule::new(vec![], vec![lit![q(a)]]));
        assert_eq!(
            rule![if q(a) and q(b) and q(c)],
            Rule::new(vec![], vec![lit![q(a)], lit![q(b)], lit![q(c)]])
        );

        // Rules generally have a (disjunctive) head and a (conjunctive) body.
        assert_eq!(rule![p if q], Rule::new(vec![lit![p]], vec![lit![q]]));
        assert_eq!(
            rule![p(a) or p(b) or p(c) if q(a) and q(b) and q(c)],
            Rule::new(
                vec![lit![p(a)], lit![p(b)], lit![p(c)]],
                vec![lit![q(a)], lit![q(b)], lit![q(c)]]
            )
        );
        assert_eq!(
            rule![p(a, b) if q(a) and not q(b)],
            Rule::new(vec![lit![p(a, b)]], vec![lit![q(a)], lit![not q(b)]])
        );
        assert_eq!(
            rule![p(a, b) if not q(a) and q(b)],
            Rule::new(vec![lit![p(a, b)]], vec![lit![not q(a)], lit![q(b)]])
        );
        assert_eq!(
            rule![0 < 1 if 0 > 1],
            Rule::new(vec![lit![0 < 1]], vec![lit![0 > 1]])
        );
    }
}
