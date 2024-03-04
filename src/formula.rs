//! Propositional formulas are strings of atomic formulas and logical connectives.
//! After grounding (replacing all variables with constant values), they may be
//! evaluated as booleans with resepect to an interpretation (a set of atoms
//! taken to be true).

use std::collections::BTreeSet;

use crate::clause::*;
use crate::ground::*;
use crate::syntax::*;

/// An interpretation is a set of atoms interpreted as true;
/// any atom not contained in the set is interpreted as false.
pub type Interpretation = BTreeSet<Atom<GroundTerm>>;

/// If a formula `f` is satisfied by interpretation `i`, e.g.,
/// if `f.eval(i) => true`, the interpretation is called
/// a _model_ of `f`. A model that is _minimal_ or _stable_
/// is also called an _answer set_.
pub type Model = Interpretation;

/// Evaluate a ground formula with respect to an interpretation (a set
/// of atoms taken as true); i.e., ask "is this interpretation a model
/// of `self`?" *Note*: this is _not_ the same as executing a logic
/// program; this kind of evaluation is used during compilation, prior
/// to execution.
pub trait Formula {
    fn atoms(&self, interp: &mut Interpretation);
    fn eval(&self, interp: &Interpretation) -> bool;
    fn is_positive(&self) -> bool;
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

    fn is_positive(&self) -> bool {
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

    fn is_positive(&self) -> bool {
        use Pool::*;
        match self {
            Interval(start, end) => start.is_positive() && end.is_positive(),
            Set(terms) => terms.iter().all(|t| t.is_positive()),
        }
    }
}

impl Formula for Atom<GroundTerm> {
    fn atoms(&self, interp: &mut Interpretation) {
        interp.insert(self.clone());
    }

    fn is_positive(&self) -> bool {
        true
    }

    fn eval(&self, interp: &Interpretation) -> bool {
        interp.contains(self)
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

    fn is_positive(&self) -> bool {
        self.is_positive()
    }

    #[allow(clippy::nonminimal_bool)]
    fn eval(&self, interp: &Interpretation) -> bool {
        use Literal::*;
        match self {
            Positive(a) => interp.contains(a),
            Negative(a) => !interp.contains(a),
            DoubleNegative(a) => !!interp.contains(a),
            Relation(x, rel, y) => rel.eval(x, y),
        }
    }
}

impl<T> Formula for Conjunction<T>
where
    T: Formula,
{
    fn atoms(&self, interp: &mut Interpretation) {
        for c in self.iter() {
            c.atoms(interp);
        }
    }

    fn is_positive(&self) -> bool {
        self.iter().all(|c| c.is_positive())
    }

    fn eval(&self, interp: &Interpretation) -> bool {
        self.iter().all(|c| c.eval(interp))
    }
}

impl<T> Formula for Disjunction<T>
where
    T: Formula,
{
    fn atoms(&self, interp: &mut Interpretation) {
        for d in self.iter() {
            d.atoms(interp);
        }
    }

    fn is_positive(&self) -> bool {
        self.iter().all(|d| d.is_positive())
    }

    fn eval(&self, interp: &Interpretation) -> bool {
        self.iter().any(|d| d.eval(interp))
    }
}

impl Formula for Clause {
    fn atoms(&self, interp: &mut Interpretation) {
        match self {
            Self::Lit(l) => l.atoms(interp),
            Self::And(c) => c.atoms(interp),
            Self::Or(d) => d.atoms(interp),
        }
    }

    fn is_positive(&self) -> bool {
        self.is_positive()
    }

    fn eval(&self, interp: &Interpretation) -> bool {
        match self {
            Self::Lit(l) => l.eval(interp),
            Self::And(c) => c.eval(interp),
            Self::Or(d) => d.eval(interp),
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
        assert_eq!(gatom![a].eval(&interp![]), false);
        assert_eq!(gatom![a].eval(&interp![gatom![a]]), true);
        assert_eq!(gatom![a].eval(&interp![gatom![b]]), false);
        assert_eq!(gatom![a].eval(&interp![gatom![a], gatom![b]]), true);
    }

    #[test]
    fn eval_literal() {
        assert_eq!(glit![a].eval(&interp![]), false);
        assert_eq!(glit![not a].eval(&interp![]), true);
        assert_eq!(glit![a].eval(&interp![gatom![a]]), true);
        assert_eq!(glit![not a].eval(&interp![gatom![a], gatom![b]]), false);
        assert_eq!(glit![a].eval(&interp![gatom![b]]), false);
        assert_eq!(glit![not a].eval(&interp![gatom![b]]), true);
        assert_eq!(glit![a].eval(&interp![gatom![a], gatom![b]]), true);
        assert_eq!(glit![not a].eval(&interp![gatom![a], gatom![b]]), false);
    }
}
