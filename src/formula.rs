//! Propositional formulas are strings of atomic formulas and logical
//! connectives, which may be evaluated as booleans with resepect to
//! an interpretation (a set of atoms taken to be true).

use std::collections::{BTreeMap, BTreeSet};

use crate::syntax::*;
use crate::values::Image as _;

/// An interpretation is a set of atoms interpreted as true;
/// any atom not contained in the set is interpreted as false.
pub type Interpretation = BTreeSet<Atom>;

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

/// Logicial formulas may have sub-structure that we will need to collect
/// or inspect. We can also evaluate or reduce them with respect to an
/// interpretation (a set of atoms taken as true), and ground them (bind
/// all variables to constant values) with respect to a set of bindings.
pub trait Formula {
    // Collectors.
    // TODO: Walkers.
    fn atoms(&self, interp: &mut Interpretation);
    fn constants(&self, universe: &mut Universe);
    fn variables(&self, names: &mut Names);

    // Predicates.
    fn is_definite(&self) -> bool;
    fn is_ground(&self) -> bool;
    fn eval(&self, interp: &Interpretation) -> bool;

    // Transformers.
    fn ground(self, bindings: &Bindings) -> Self;
    fn reduce(self, interp: &Interpretation) -> Self;
}

impl Formula for Pool {
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

    fn constants(&self, universe: &mut Universe) {
        universe.extend(self.image());
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

    fn is_definite(&self) -> bool {
        use Pool::*;
        match self {
            Interval(start, end) => start.is_definite() && end.is_definite(),
            Set(terms) => terms.iter().all(|t| t.is_definite()),
        }
    }

    fn is_ground(&self) -> bool {
        use Pool::*;
        match self {
            Interval(start, end) => start.is_ground() && end.is_ground(),
            Set(terms) => terms.iter().all(|t| t.is_ground()),
        }
    }

    fn eval(&self, _interp: &Interpretation) -> bool {
        todo!()
    }

    fn ground(self, bindings: &Bindings) -> Self {
        use Pool::*;
        match self {
            Interval(start, end) => Self::interval(start.ground(bindings), end.ground(bindings)),
            Set(terms) => Self::set(terms.into_iter().map(|t| t.ground(bindings))),
        }
    }

    fn reduce(self, _interp: &Interpretation) -> Self {
        todo!()
    }
}

impl Formula for Term {
    #[allow(clippy::only_used_in_recursion)]
    fn atoms(&self, interp: &mut Interpretation) {
        use Term::*;
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

    fn is_definite(&self) -> bool {
        true
    }

    fn is_ground(&self) -> bool {
        use Term::*;
        match self {
            Constant(..) | Choice(..) => true,
            Variable(..) => false,
            UnaryOperation(_op, x) => x.is_ground(),
            BinaryOperation(x, _op, y) => x.is_ground() && y.is_ground(),
        }
    }

    fn eval(&self, _interp: &Interpretation) -> bool {
        use Term::*;
        match self {
            Constant(..) => true,
            Variable(..) => false,
            Choice(..) => todo!("eval({self})"),
            UnaryOperation(..) => todo!("eval({self})"),
            BinaryOperation(..) => todo!("eval({self})"),
        }
    }

    fn ground(self, bindings: &Bindings) -> Self {
        use Term::*;
        match self {
            Constant(..) | Choice(..) => self,
            Variable(name) => Constant(bindings[&name].clone()),
            UnaryOperation(op, x) => Self::unary_operation(op, x.ground(bindings)),
            BinaryOperation(x, op, y) => {
                Self::binary_operation(x.ground(bindings), op, y.ground(bindings))
            }
        }
    }

    fn reduce(self, _interp: &Interpretation) -> Self {
        self
    }
}

impl Formula for Atom {
    fn atoms(&self, interp: &mut Interpretation) {
        interp.insert(self.clone());
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

    fn is_definite(&self) -> bool {
        true
    }

    /// An atom is ground if its arguments are all ground.
    /// An arity 0 predicate is therefore always ground.
    fn is_ground(&self) -> bool {
        self.arguments.iter().all(|arg| arg.is_ground())
    }

    fn eval(&self, interp: &Interpretation) -> bool {
        interp.contains(self)
    }

    fn ground(self, bindings: &Bindings) -> Self {
        Self::new(
            self.predicate,
            self.arguments.into_iter().map(|arg| arg.ground(bindings)),
        )
    }

    fn reduce(self, _interp: &Interpretation) -> Self {
        self
    }
}

impl Formula for Literal {
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

    fn is_definite(&self) -> bool {
        use Literal::*;
        match self {
            Positive(..) | Relation(..) => true,
            Negative(..) | DoubleNegative(..) => false,
        }
    }

    fn is_ground(&self) -> bool {
        use Literal::*;
        match self {
            Positive(a) | Negative(a) | DoubleNegative(a) => a.is_ground(),
            Relation(x, _rel, y) => x.is_ground() && y.is_ground(),
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

    fn ground(self, bindings: &Bindings) -> Self {
        use Literal::*;
        match self {
            Positive(a) => Positive(a.ground(bindings)),
            Negative(a) => Negative(a.ground(bindings)),
            DoubleNegative(a) => DoubleNegative(a.ground(bindings)),
            Relation(x, rel, y) => Self::relation(x.ground(bindings), rel, y.ground(bindings)),
        }
    }

    fn reduce(self, _interp: &Interpretation) -> Self {
        self
    }
}

impl Formula for Rule {
    fn atoms(&self, interp: &mut Interpretation) {
        for h in &self.head {
            h.atoms(interp);
        }
        for b in &self.body {
            b.atoms(interp);
        }
    }

    fn constants(&self, universe: &mut Universe) {
        for h in &self.head {
            h.constants(universe);
        }
        for b in &self.body {
            b.constants(universe);
        }
    }

    fn variables(&self, names: &mut Names) {
        for h in &self.head {
            h.variables(names);
        }
        for b in &self.body {
            b.variables(names);
        }
    }

    fn is_definite(&self) -> bool {
        self.head.iter().all(|h| h.is_definite()) && self.body.iter().all(|b| b.is_definite())
    }

    fn is_ground(&self) -> bool {
        self.head.iter().all(|h| h.is_ground()) && self.body.iter().all(|b| b.is_ground())
    }

    fn eval(&self, interp: &Interpretation) -> bool {
        self.head.iter().any(|h| h.eval(interp)) && self.body.iter().all(|b| b.eval(interp))
    }

    fn ground(self, _bindings: &Bindings) -> Self {
        todo!("ground rule")
    }

    fn reduce(self, _interp: &Interpretation) -> Self {
        todo!("reduce rule")
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

    #[test]
    fn eval_rule() {
        assert_eq!(rule![a].eval(&interp![]), false);
        assert_eq!(rule![a].eval(&interp![atom![a]]), true);
        assert_eq!(rule![a or b].eval(&interp![atom![b]]), true);
        assert_eq!(rule![a if a].eval(&interp![atom![a]]), true);
        assert_eq!(rule![a if b].eval(&interp![atom![a], atom![b]]), true);
        assert_eq!(
            rule![a if b and c].eval(&interp![atom![a], atom![b]]),
            false
        );
    }
}
