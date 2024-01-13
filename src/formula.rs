//! Propositional formulas are strings of atomic formulas and logical
//! connectives, which may be evaluated as booleans with resepect to
//! an interpretation (a set of atoms taken to be true).

use std::collections::HashSet;

use crate::syntax::*;

/// An interpretation is a set of atoms interpreted as true;
/// any atom not contained in the set is interpreted as false.
/// If a formula `f` is satisfied by interpretation `i`, e.g.,
/// if `f.eval(i) => true`, then the interpretation is called
/// a _model_ of `f`. If the model is "minimal", then it is called
/// a _stable_ model, also known as an _answer set_.
pub type Interpretation = HashSet<Atom>;

/// Logicial formulas (which may be "atomic") have sub-structure
/// that we will sometimes need to collect or inspect. We can also
/// evaluate them with respect to an interpretation (a set of atoms
/// taken as true).
// TODO: walkers.
pub trait Formula {
    fn atoms(&self) -> Vec<Atom>;
    fn constants(&self) -> Vec<Constant>;
    fn is_definite(&self) -> bool;
    fn is_ground(&self) -> bool;
    fn eval(&self, interp: &Interpretation) -> bool;
    fn uniq_atoms(&self) -> HashSet<Atom> {
        self.atoms().into_iter().collect()
    }
}

impl Formula for Atom {
    fn atoms(&self) -> Vec<Atom> {
        vec![self.clone()]
    }

    fn constants(&self) -> Vec<Constant> {
        self.arguments
            .iter()
            .filter_map(|term| match term {
                Term::Constant(c) => Some(c.clone()),
                Term::Variable(_) => None,
            })
            .collect()
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
}

impl Formula for Literal {
    fn atoms(&self) -> Vec<Atom> {
        match self {
            Literal::Positive(atom) | Literal::Negative(atom) => vec![atom.clone()],
        }
    }

    fn constants(&self) -> Vec<Constant> {
        match self {
            Self::Positive(atom) | Self::Negative(atom) => atom.constants(),
        }
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
}

impl Formula for Rule {
    fn atoms(&self) -> Vec<Atom> {
        self.head
            .iter()
            .flat_map(|h| h.atoms())
            .chain(self.body.iter().flat_map(|b| b.atoms()))
            .collect()
    }

    fn constants(&self) -> Vec<Constant> {
        self.head
            .iter()
            .flat_map(|h| h.constants())
            .chain(self.body.iter().flat_map(|b| b.constants()))
            .collect()
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
