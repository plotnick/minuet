//! Syntactic elements of a simple logic programming language.
//! A string or macro parser may layer whatever surface syntax
//! it likes on top of these elements.

use std::fmt;

/// Uninterpreted element that names a constant, variable, or predicate.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
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

macro_rules! sym {
    [$s:ident] => {
        Symbol::new(String::from(stringify!($s)))
    };
}

#[test]
fn symbol() {
    assert_eq!(sym![a], Symbol::new(String::from("a")));
}

// TODO: enum Constant { Name(Symbol), Integer(i64), String(String), ... }
pub type Constant = Symbol;

/// Interpreted element that represents either itself (a constant)
/// or something else (a variable).
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Term {
    Constant(Symbol),
    Variable(Symbol),
}

impl Term {
    pub fn is_constant(&self) -> bool {
        match self {
            Self::Constant(_) => true,
            Self::Variable(_) => false,
        }
    }

    #[allow(dead_code)]
    pub fn is_variable(&self) -> bool {
        !self.is_constant()
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Constant(s) | Term::Variable(s) => s.fmt(f),
        }
    }
}

/// Prolog surface syntax: names of constants start with a lowercase
/// letter, the names of variables start with an uppercase letter or
/// underscore.
macro_rules! term {
    [$s:ident] => {
        if stringify!($s).chars().take(1).all(char::is_lowercase) {
            Term::Constant(sym![$s])
        } else {
            Term::Variable(sym![$s])
        }
    };
}

#[test]
fn term() {
    assert_eq!(term![a], Term::Constant(Symbol::new(String::from("a"))));
    assert_eq!(term![X], Term::Variable(Symbol::new(String::from("X"))));
}

/// An "atomic formula" is a predicate (_n_-ary relation) applied to
/// a tuple of terms. If _n_ = 0, we may elide the argument tuple.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Atom {
    pub predicate: Symbol,
    pub arguments: Vec<Term>,
}

impl Atom {
    pub fn new(predicate: Symbol, arguments: Vec<Term>) -> Self {
        Self {
            predicate,
            arguments,
        }
    }
}

impl fmt::Display for Atom {
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

macro_rules! atom {
    [$pred:ident] => {
        Atom::new(sym![$pred], vec![])
    };
    [$pred:ident($($arg:tt),*)] => {
        Atom::new(sym![$pred], vec![$(term![$arg]),*])
    };
}

#[test]
fn atom() {
    assert_eq!(atom![f], Atom::new(sym![f], vec![]));
    assert_eq!(atom![f()], Atom::new(sym![f], vec![]));
    assert_eq!(atom![f(a)], Atom::new(sym![f], vec![term![a]]));
    assert_eq!(atom![f(X, Y)], Atom::new(sym![f], vec![term![X], term![Y]]));
}

/// An atomic formula or its negation (as failure).
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Literal {
    Positive(Atom),
    Negative(Atom),
}

#[allow(dead_code)]
impl Literal {
    pub fn negate(&self) -> Self {
        match self {
            Self::Positive(atom) => Self::Negative(atom.clone()),
            Self::Negative(atom) => Self::Positive(atom.clone()),
        }
    }

    pub fn is_positive(&self) -> bool {
        match self {
            Self::Positive(_) => true,
            Self::Negative(_) => false,
        }
    }

    pub fn is_negative(&self) -> bool {
        !self.is_positive()
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Literal::Positive(atom) => f.write_fmt(format_args!("{}", atom)),
            Literal::Negative(atom) => f.write_fmt(format_args!("not {}", atom)),
        }
    }
}

macro_rules! lit {
    [$pred:ident$(($($arg:tt),*))?] => {
        Literal::Positive(atom![$pred$(($($arg),*))?])
    };
    [not $pred:ident$(($($arg:tt),*))?] => {
        Literal::Negative(atom![$pred$(($($arg),*))?])
    };
}

#[test]
fn literal() {
    assert_eq!(lit![p(a, b)], Literal::Positive(atom![p(a, b)]));
    assert_eq!(lit![not p(a, b)], Literal::Negative(atom![p(a, b)]));
}

/// A rule has a disjunctive head and conjunctive body, either
/// of which may be empty. Negations may occur only in the body.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Rule {
    pub head: Vec<Atom>,
    pub body: Vec<Literal>,
}

impl Rule {
    pub fn new(head: Vec<Atom>, body: Vec<Literal>) -> Self {
        Self { head, body }
    }
}

macro_rules! rule {
    // TODO: Is there a way to accumulate forward and avoid this reverse?
    [@head [] -> [$($head:tt)*]] => {{
        let mut head = vec![$($head)*];
        head.reverse();
        head
    }};
    [@head [$pred:ident$(($($arg:tt),*))?] -> [$($head:tt)*]] => {
        rule![@head [] -> [atom![$pred$(($($arg),*))?], $($head)*]]
    };
    [@head [$pred:ident$(($($arg:tt),*))? or $($rest:tt)*] -> [$($head:tt)*]] => {
        rule![@head [$($rest)*] -> [atom![$pred$(($($arg),*))?], $($head)*]]
    };

    // TODO: ditto
    [@body [] -> [$($body:tt)*]] => {{
        let mut body = vec![$($body)*];
        body.reverse();
        body
    }};
    [@body [$pred:ident$(($($arg:tt),*))?] -> [$($body:tt)*]] => {
        rule![@body [] -> [lit![$pred$(($($arg),*))?], $($body)*]]
    };
    [@body [not $pred:ident$(($($arg:tt),*))?] -> [$($body:tt)*]] => {
        rule![@body [] -> [lit![not $pred$(($($arg),*))?], $($body)*]]
    };
    [@body [$pred:ident$(($($arg:tt),*))? and $($rest:tt)*] -> [$($body:tt)*]] => {
        rule![@body [$($rest)*] -> [lit![$pred$(($($arg),*))?], $($body)*]]
    };
    [@body [not $pred:ident$(($($arg:tt),*))? and $($rest:tt)*] -> [$($body:tt)*]] => {
        rule![@body [$($rest)*] -> [lit![not $pred$(($($arg),*))?], $($body)*]]
    };

    [if $($body:tt)*] => {
        Rule::new(vec![], rule![@body [$($body)*] -> []])
    };
    [$pred:ident$(($($arg:tt),*))?] => {
        Rule::new(rule![@head [$pred$(($($arg),*))?] -> []], vec![])
    };
    [$pred:ident$(($($arg:tt),*))? or $($rest:tt)*] => {
        Rule::new(rule![@head [$pred$(($($arg),*))? or $($rest)*] -> []], vec![])
    };
    [($pred:ident$(($($arg:tt),*))? or $($rest:tt)*)] => {
        Rule::new(rule![@head [$pred$(($($arg),*))? or $($rest)*] -> []], vec![])
    };
    [$pred:ident$(($($arg:tt),*))? if $($body:tt)*] => {
        Rule::new(rule![@head [$pred$(($($arg),*))?] -> []], rule![@body [$($body)*] -> []])
    };
    [($pred:ident$(($($arg:tt),*))? or $($rest:tt)*) if $($body:tt)*] => {
        Rule::new(rule![@head [$pred$(($($arg),*))? or $($rest)*] -> []], rule![@body [$($body)*] -> []])
    };
}

#[test]
fn rule() {
    // Heads with no bodies are (disjunctive) "facts".
    assert_eq!(rule![p], Rule::new(vec![atom![p]], vec![]));
    assert_eq!(rule![p(a)], Rule::new(vec![atom![p(a)]], vec![]));
    assert_eq!(
        rule![p(a) or p(b)],
        Rule::new(vec![atom![p(a)], atom![p(b)]], vec![])
    );

    // Bodies without heads are (conjunctive) "constraints".
    assert_eq!(rule![if q(a)], Rule::new(vec![], vec![lit![q(a)]]));
    assert_eq!(
        rule![if q(a) and q(b) and q(c)],
        Rule::new(vec![], vec![lit![q(a)], lit![q(b)], lit![q(c)]])
    );

    // Rules generally have a (disjunctive) head and a (conjunctive) body.
    assert_eq!(rule![p if q], Rule::new(vec![atom![p]], vec![lit![q]]));
    assert_eq!(
        rule![(p(a) or p(b) or p(c)) if q(a) and q(b) and q(c)],
        Rule::new(
            vec![atom![p(a)], atom![p(b)], atom![p(c)]],
            vec![lit![q(a)], lit![q(b)], lit![q(c)]]
        )
    );
    assert_eq!(
        rule![p(a, b) if q(a) and not q(b)],
        Rule::new(vec![atom![p(a, b)]], vec![lit![q(a)], lit![not q(b)]])
    );
    assert_eq!(
        rule![p(a, b) if not q(a) and q(b)],
        Rule::new(vec![atom![p(a, b)]], vec![lit![not q(a)], lit![q(b)]])
    );
}
