//! Propositional formulas are strings of atomic formulas and logical
//! connectives. After grounding (binding all variables to constant
//! values), they may be evaluated as booleans with resepect to an
//! interpretation (a set of atoms taken to be true).

use std::collections::{BTreeMap, BTreeSet};

use crate::syntax::*;
use crate::values::Image as _;

/// An interpretation is a set of atoms interpreted as true;
/// any atom not contained in the set is interpreted as false.
pub type Interpretation = BTreeSet<Atom<GroundTerm>>;

/// If a formula `f` is satisfied by interpretation `i`, e.g.,
/// if `f.eval(i) => true`, then the interpretation is called
/// a _model_ of `f`. A model that is _minimal_ or _stable_
/// is also called an _answer set_.
pub type Model = Interpretation;

/// Map variable names to constant values (to ground them).
pub type Bindings = BTreeMap<Symbol, Constant>;

/// A set of variable names (to ground).
pub type Names = BTreeSet<Symbol>;

/// The _Herbrand Universe_ is the set of all constants in a program.
/// It is the source of values to which variables may be bound.
pub type Universe = BTreeSet<Constant>;

/// Terms that can include variables may be _grounded_, where we replace
/// all variables with all possible values that may be bound to them.
///
/// The `Ground` type represents the _result_ of the grounding, e.g.,
/// we go from `NormalRule<Term>` → `NormalRule<GroundTerm>` via:
/// ```
/// impl Groundable for NormalRule<Term> {
///     type Ground = NormalRule<GroundTerm>;
///     ...
/// }
/// ```
pub trait Groundable {
    type Ground;

    fn is_ground(&self) -> bool;
    fn ground(self, bindings: &Bindings) -> Self::Ground;
    fn ground_new(self) -> Self::Ground
    where
        Self: Sized,
    {
        self.ground(&Bindings::new())
    }
    fn constants(&self, universe: &mut Universe);
    fn variables(&self, names: &mut Names);
}

impl Groundable for Term {
    type Ground = GroundTerm;

    fn is_ground(&self) -> bool {
        use Term::*;
        match self {
            Constant(_) => true,
            Variable(_) => false,
            Choice(p) => p.is_ground(),
            UnaryOperation(_op, x) => x.is_ground(),
            BinaryOperation(x, _op, y) => x.is_ground() && y.is_ground(),
        }
    }

    fn ground(self, bindings: &Bindings) -> GroundTerm {
        match self {
            Term::Constant(c) => GroundTerm::Constant(c),
            Term::Choice(p) => GroundTerm::Choice(p.ground(bindings)),
            Term::Variable(name) => GroundTerm::Constant(bindings[&name].clone()),
            Term::UnaryOperation(op, x) => GroundTerm::unary_operation(op, x.ground(bindings)),
            Term::BinaryOperation(x, op, y) => {
                GroundTerm::binary_operation(x.ground(bindings), op, y.ground(bindings))
            }
        }
    }

    fn constants(&self, universe: &mut Universe) {
        use Term::*;
        match self {
            Constant(c) => universe.extend([c.clone()]),
            Choice(c) => c.constants(universe),
            Variable(..) | BinaryOperation(..) | UnaryOperation(..) => (),
        }
    }

    fn variables(&self, names: &mut Names) {
        if let Term::Variable(v) = self {
            names.insert(v.clone());
        }
    }
}

impl Groundable for Pool<Term> {
    type Ground = Pool<GroundTerm>;

    fn is_ground(&self) -> bool {
        use Pool::*;
        match self {
            Interval(start, end) => start.is_ground() && end.is_ground(),
            Set(terms) => terms.iter().all(|t| t.is_ground()),
        }
    }

    fn ground(self, bindings: &Bindings) -> Self::Ground {
        use Pool::*;
        match self {
            Interval(start, end) => {
                Self::Ground::interval(start.ground(bindings), end.ground(bindings))
            }
            Set(terms) => Self::Ground::set(terms.into_iter().map(|t| t.ground(bindings))),
        }
    }

    fn constants(&self, universe: &mut Universe) {
        // TODO: Insufficiently instantiated intervals like `0..X`
        // are program errors, and should cause processing to stop.
        universe.extend(self.clone().ground_new().image());
    }

    fn variables(&self, names: &mut Names) {
        use Pool::*;
        match self {
            Interval(start, end) => {
                start.variables(names);
                end.variables(names);
            }
            Set(terms) => {
                for term in terms {
                    term.variables(names);
                }
            }
        }
    }
}

/// We can evaluate or reduce ground formulas with respect to
/// an interpretation (a set of atoms taken as true).
pub trait Formula {
    fn atoms(&self, interp: &mut Interpretation);
    fn eval(&self, interp: &Interpretation) -> bool;
    fn is_definite(&self) -> bool;
}

impl Formula for GroundTerm {
    #[allow(clippy::only_used_in_recursion)]
    fn atoms(&self, interp: &mut Interpretation) {
        use GroundTerm::*;
        match self {
            UnaryOperation(_op, x) => {
                x.atoms(interp);
            }
            BinaryOperation(x, _op, y) => {
                x.atoms(interp);
                y.atoms(interp);
            }
            _ => (),
        }
    }

    fn eval(&self, _interp: &Interpretation) -> bool {
        todo!()
    }

    fn is_definite(&self) -> bool {
        todo!()
    }
}

impl Formula for Pool<GroundTerm> {
    fn atoms(&self, interp: &mut Interpretation) {
        use Pool::*;
        match self {
            Interval(start, end) => {
                start.atoms(interp);
                end.atoms(interp);
            }
            Set(terms) => {
                for term in terms {
                    term.atoms(interp);
                }
            }
        }
    }

    fn eval(&self, _interp: &Interpretation) -> bool {
        todo!()
    }

    fn is_definite(&self) -> bool {
        use Pool::*;
        match self {
            Interval(start, end) => start.is_definite() && end.is_definite(),
            Set(terms) => terms.iter().all(|t| t.is_definite()),
        }
    }
}

impl Formula for Atom<GroundTerm> {
    fn atoms(&self, interp: &mut Interpretation) {
        interp.insert(self.clone());
    }

    fn is_definite(&self) -> bool {
        true
    }

    fn eval(&self, interp: &Interpretation) -> bool {
        interp.contains(self)
    }
}

impl Groundable for Atom<Term> {
    type Ground = Atom<GroundTerm>;

    /// An atom is ground if its arguments are all ground.
    /// An arity 0 predicate is therefore always ground.
    fn is_ground(&self) -> bool {
        self.arguments.iter().all(|arg| arg.is_ground())
    }

    fn ground(self, bindings: &Bindings) -> Self::Ground {
        Self::Ground::new(
            self.predicate,
            self.arguments.into_iter().map(|arg| arg.ground(bindings)),
        )
    }

    fn constants(&self, universe: &mut Universe) {
        for arg in &self.arguments {
            arg.constants(universe);
        }
    }

    fn variables(&self, names: &mut Names) {
        for arg in &self.arguments {
            arg.variables(names);
        }
    }
}

impl Formula for Literal<GroundTerm> {
    fn atoms(&self, interp: &mut Interpretation) {
        use Literal::*;
        match self {
            Positive(a) | Negative(a) | DoubleNegative(a) => a.atoms(interp),
            Relation(x, _rel, y) => {
                x.atoms(interp);
                y.atoms(interp);
            }
        }
    }

    fn is_definite(&self) -> bool {
        use Literal::*;
        match self {
            Positive(..) | Relation(..) => true,
            Negative(..) | DoubleNegative(..) => false,
        }
    }

    #[allow(clippy::nonminimal_bool)]
    fn eval(&self, interp: &Interpretation) -> bool {
        use Literal::*;
        use RelOp::*;
        match self {
            Positive(a) => interp.contains(a),
            Negative(a) => !interp.contains(a),
            DoubleNegative(a) => !!interp.contains(a),
            Relation(x, rel, y) => {
                let x = x.image();
                let y = y.image();
                match rel {
                    Eq => x == y,
                    Ne => x != y,
                    Lt => x < y,
                    Gt => x > y,
                    Leq => x <= y,
                    Geq => x >= y,
                }
            }
        }
    }
}

impl Groundable for Literal<Term> {
    type Ground = Literal<GroundTerm>;

    fn is_ground(&self) -> bool {
        use Literal::*;
        match self {
            Positive(a) | Negative(a) | DoubleNegative(a) => a.is_ground(),
            Relation(x, _rel, y) => x.is_ground() && y.is_ground(),
        }
    }

    fn ground(self, bindings: &Bindings) -> Self::Ground {
        use Literal::*;
        match self {
            Positive(a) => Positive(a.ground(bindings)),
            Negative(a) => Negative(a.ground(bindings)),
            DoubleNegative(a) => DoubleNegative(a.ground(bindings)),
            Relation(x, rel, y) => Literal::relation(x.ground(bindings), rel, y.ground(bindings)),
        }
    }

    fn constants(&self, universe: &mut Universe) {
        use Literal::*;
        match self {
            Positive(a) | Negative(a) | DoubleNegative(a) => a.constants(universe),
            Relation(x, _rel, y) => {
                x.constants(universe);
                y.constants(universe);
            }
        }
    }

    fn variables(&self, names: &mut Names) {
        use Literal::*;
        match self {
            Positive(a) | Negative(a) | DoubleNegative(a) => a.variables(names),
            Relation(x, _rel, y) => {
                x.variables(names);
                y.variables(names);
            }
        }
    }
}

#[cfg(test)]
mod test {
    #![allow(clippy::bool_assert_comparison)]

    use super::*;

    macro_rules! interp {
        [] => { Interpretation::new() };
        [$($atom:expr),+] => {{
            let mut interp = Interpretation::new();
            interp.extend([$($atom),+]);
            interp
        }};
    }

    #[test]
    fn eval_atom() {
        assert_eq!(atom![a].eval(&interp![]), false);
        assert_eq!(atom![a].eval(&interp![atom![a]]), true);
        assert_eq!(atom![a].eval(&interp![atom![b]]), false);
        assert_eq!(atom![a].eval(&interp![atom![a], atom![b]]), true);
    }

    #[test]
    fn eval_literal() {
        assert_eq!(lit![a].eval(&interp![]), false);
        assert_eq!(lit![not a].eval(&interp![]), true);
        assert_eq!(lit![a].eval(&interp![atom![a]]), true);
        assert_eq!(lit![not a].eval(&interp![atom![a]]), false);
        assert_eq!(lit![a].eval(&interp![atom![b]]), false);
        assert_eq!(lit![not a].eval(&interp![atom![b]]), true);
        assert_eq!(lit![a].eval(&interp![atom![a], atom![b]]), true);
        assert_eq!(lit![not a].eval(&interp![atom![a], atom![b]]), false);
    }
}
