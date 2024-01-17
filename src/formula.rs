//! Propositional formulas are strings of atomic formulas and logical
//! connectives, which may be evaluated as booleans with resepect to
//! an interpretation (a set of atoms taken to be true).

use std::collections::{BTreeMap, BTreeSet};

use crate::syntax::*;

/// An interpretation is a set of atoms interpreted as true;
/// any atom not contained in the set is interpreted as false.
/// If a formula `f` is satisfied by interpretation `i`, e.g.,
/// if `f.eval(i) => true`, then the interpretation is called
/// a _model_ of `f`. If the model is "minimal", then it is called
/// a _stable_ model, also known as an _answer set_.
pub type Interpretation = BTreeSet<Atom>;

/// Map variable names to constant values for grounding.
pub type Bindings = BTreeMap<Symbol, Constant>;

/// A set of variable names.
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

impl Formula for Atom {
    fn atoms(&self, interp: &mut Interpretation) {
        interp.insert(self.clone());
    }

    fn constants(&self, universe: &mut Universe) {
        for arg in &self.arguments {
            if let Term::Constant(c) = arg {
                universe.insert(c.clone());
            }
        }
    }

    fn variables(&self, names: &mut Names) {
        for arg in &self.arguments {
            if let Term::Variable(v) = arg {
                names.insert(v.clone());
            }
        }
    }

    fn is_definite(&self) -> bool {
        true
    }

    /// An atom is ground if its arguments are all constant.
    /// (An arity 0 predicate is therefore always ground.)
    fn is_ground(&self) -> bool {
        self.arguments.iter().all(Term::is_constant)
    }

    fn eval(&self, interp: &Interpretation) -> bool {
        interp.contains(self)
    }

    fn ground(self, bindings: &Bindings) -> Self {
        Self::new(
            self.predicate,
            self.arguments.into_iter().map(|arg| match arg {
                Term::Constant(sym) => Term::Constant(sym),
                Term::Variable(sym) => Term::Constant(bindings[&sym].clone()),
            }),
        )
    }

    fn reduce(self, _interp: &Interpretation) -> Self {
        self
    }
}

impl Formula for Literal {
    fn atoms(&self, interp: &mut Interpretation) {
        self.atom().atoms(interp);
    }

    fn constants(&self, universe: &mut Universe) {
        self.atom().constants(universe);
    }

    fn variables(&self, names: &mut Names) {
        self.atom().variables(names);
    }

    fn is_definite(&self) -> bool {
        self.is_positive()
    }

    fn is_ground(&self) -> bool {
        match self {
            Self::Positive(atom) | Self::Negative(atom) => atom.is_ground(),
        }
    }

    fn eval(&self, interp: &Interpretation) -> bool {
        match self {
            Self::Positive(atom) => interp.contains(atom),
            Self::Negative(atom) => !interp.contains(atom),
        }
    }

    fn ground(self, bindings: &Bindings) -> Self {
        match self {
            Self::Positive(atom) => Self::Positive(atom.ground(bindings)),
            Self::Negative(atom) => Self::Negative(atom.ground(bindings)),
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
