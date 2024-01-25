//! Propositional formulas are strings of atomic formulas and logical connectives.
//! After grounding (replacing all variables with constant values), they may be
//! evaluated as booleans with resepect to an interpretation (a set of atoms
//! taken to be true).

use std::collections::{BTreeMap, BTreeSet};

use crate::clause::*;
use crate::syntax::*;
use crate::values::Values as _;

/// An interpretation is a set of atoms interpreted as true;
/// any atom not contained in the set is interpreted as false.
pub type Interpretation = BTreeSet<Atom<GroundTerm>>;

/// If a formula `f` is satisfied by interpretation `i`, e.g.,
/// if `f.eval(i) => true`, the interpretation is called
/// a _model_ of `f`. A model that is _minimal_ or _stable_
/// is also called an _answer set_.
pub type Model = Interpretation;

/// Map variable names to constant values (in order to ground them).
pub type Bindings = BTreeMap<Symbol, Constant>;

/// A set of variable names (to ground).
pub type Names = BTreeSet<Symbol>;

/// The _Herbrand Universe_ is the set of all constants in a program.
/// It is the set of values to which variables may be bound.
pub type Universe = BTreeSet<Constant>;

/// Terms that can include variables may be _grounded_, wherein we replace
/// all variables with all possible values that can be bound to them.
///
/// The `Ground` associated type represents the _result_ of the grounding,
/// e.g., we go from `Rule<Term>` → `Rule<GroundTerm>` via (mod type aliases):
/// ```
/// impl Groundable for Rule<Term> {
///     type Ground = Rule<GroundTerm>;
///     ...
/// }
/// ```
pub trait Groundable {
    type Ground;

    fn is_ground(&self) -> bool;
    fn ground_with(self, bindings: &Bindings) -> Self::Ground;
    fn ground(self) -> Self::Ground
    where
        Self: Sized,
    {
        self.ground_with(&Bindings::new())
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

    fn ground_with(self, bindings: &Bindings) -> GroundTerm {
        match self {
            Term::Constant(c) => GroundTerm::Constant(c),
            Term::Choice(p) => GroundTerm::Choice(p.ground_with(bindings)),
            Term::Variable(name) => GroundTerm::Constant(bindings[&name].clone()),
            Term::UnaryOperation(op, x) => GroundTerm::unary_operation(op, x.ground_with(bindings)),
            Term::BinaryOperation(x, op, y) => {
                GroundTerm::binary_operation(x.ground_with(bindings), op, y.ground_with(bindings))
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

    fn ground_with(self, bindings: &Bindings) -> Self::Ground {
        use Pool::*;
        match self {
            Interval(start, end) => {
                Self::Ground::interval(start.ground_with(bindings), end.ground_with(bindings))
            }
            Set(terms) => Self::Ground::set(terms.into_iter().map(|t| t.ground_with(bindings))),
        }
    }

    fn constants(&self, universe: &mut Universe) {
        use Pool::*;
        match self {
            Interval(i, j) if i.is_ground() && j.is_ground() => {
                universe.extend(self.clone().ground().values())
            }
            Interval(i, j) => todo!("insufficiently instantiated interval {i}..{j}"),
            Set(terms) => {
                for term in terms {
                    term.constants(universe);
                }
            }
        }
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

/// Auxiliary atoms are already ground.
impl Groundable for Auxiliary {
    type Ground = Auxiliary;

    fn is_ground(&self) -> bool {
        true
    }
    fn ground_with(self, _: &Bindings) -> Self::Ground {
        self
    }
    fn constants(&self, _: &mut Universe) {}
    fn variables(&self, _: &mut Names) {}
}

impl Groundable for Aggregate<Term> {
    type Ground = Aggregate<GroundTerm>;

    /// An aggregate is ground if all of its choices are ground.
    fn is_ground(&self) -> bool {
        self.choices.iter().all(|choice| choice.is_ground())
    }

    fn ground_with(self, bindings: &Bindings) -> Self::Ground {
        Self::Ground {
            choices: self
                .choices
                .into_iter()
                .map(|choice| choice.ground_with(bindings))
                .collect(),
        }
    }

    fn constants(&self, universe: &mut Universe) {
        for choice in &self.choices {
            choice.constants(universe);
        }
    }

    fn variables(&self, names: &mut Names) {
        for choice in &self.choices {
            choice.variables(names);
        }
    }
}

impl Groundable for Application<Term> {
    type Ground = Application<GroundTerm>;

    /// A predicate application is ground if all of its arguments are ground.
    /// An arity 0 predicate is therefore always ground.
    fn is_ground(&self) -> bool {
        self.arguments.iter().all(|arg| arg.is_ground())
    }

    fn ground_with(self, bindings: &Bindings) -> Self::Ground {
        Self::Ground {
            predicate: self.predicate,
            arguments: self
                .arguments
                .into_iter()
                .map(|arg| arg.ground_with(bindings))
                .collect(),
        }
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

impl Groundable for Atom<Term> {
    type Ground = Atom<GroundTerm>;

    fn is_ground(&self) -> bool {
        use Atom::*;
        match self {
            Aux(..) => true,
            Agg(agg) => agg.is_ground(),
            App(app) => app.is_ground(),
        }
    }

    fn ground_with(self, bindings: &Bindings) -> Self::Ground {
        use Atom::*;
        match self {
            Aux(aux) => Self::Ground::Aux(aux.ground_with(bindings)),
            Agg(agg) => Self::Ground::Agg(agg.ground_with(bindings)),
            App(app) => Self::Ground::App(app.ground_with(bindings)),
        }
    }

    fn constants(&self, universe: &mut Universe) {
        use Atom::*;
        match self {
            Aux(aux) => aux.constants(universe),
            Agg(agg) => agg.constants(universe),
            App(app) => app.constants(universe),
        }
    }

    fn variables(&self, names: &mut Names) {
        use Atom::*;
        match self {
            Aux(aux) => aux.variables(names),
            Agg(agg) => agg.variables(names),
            App(app) => app.variables(names),
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

impl Groundable for Literal<Term> {
    type Ground = Literal<GroundTerm>;

    fn is_ground(&self) -> bool {
        use Literal::*;
        match self {
            Positive(a) | Negative(a) | DoubleNegative(a) => a.is_ground(),
            Relation(x, _rel, y) => x.is_ground() && y.is_ground(),
        }
    }

    fn ground_with(self, bindings: &Bindings) -> Self::Ground {
        use Literal::*;
        match self {
            Positive(a) => Positive(a.ground_with(bindings)),
            Negative(a) => Negative(a.ground_with(bindings)),
            DoubleNegative(a) => DoubleNegative(a.ground_with(bindings)),
            Relation(x, rel, y) => {
                Literal::relation(x.ground_with(bindings), rel, y.ground_with(bindings))
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
