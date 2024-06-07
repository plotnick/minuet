//! A trait to describe elements that may be grounded.

use minuet_syntax::*;

use crate::program::{BaseProgram, GroundProgram, Program};
use crate::values::{Value, Values as _};

use super::{
    Bindings, ExhaustiveGrounder, Functions, GroundTerm, Grounder, GroundingError, Names, Universe,
};

/// Syntactic elements that contain variables can be _grounded_, where we
/// replace variables with the values that they may be bound to. This trait
/// represents elements for which such replacement is possible: it enables
/// gathering the data needed for grounding and performing the replacments
/// for a particular set of [`Bindings`]. It does _not_ attempt to describe
/// how to choose the [`Bindings`] sets; that's the job of a [`Grounder`].
pub trait Groundable {
    type Ground;
    type Error;

    /// Return `true` if the element is already ground.
    fn is_ground(&self) -> bool;

    /// Perform the bindings in [`Bindings`] and return a grounded
    /// (or more nearly grounded) element. Intended only to be called
    /// by [`Grounder::ground`].
    fn ground_with(self, bindings: &Bindings) -> Result<Self::Ground, Self::Error>;

    /// Convenience method: ground with an empty set of bindings.
    /// Trivially grounds any element for which [`Self::is_ground`]
    /// returns true.
    fn ground(self) -> Result<Self::Ground, Self::Error>
    where
        Self: Sized,
    {
        self.ground_with(&Bindings::new())
    }

    /// Collect the constants occuring in this element.
    fn constants(&self, universe: &mut Universe);

    /// Collect the variables occuring in this element.
    fn variables(&self, names: &mut Names);

    /// Collect the functions occuring in this element.
    fn functions(&self, functions: &mut Functions);
}

impl Groundable for Term {
    type Ground = GroundTerm;
    type Error = GroundingError;

    fn is_ground(&self) -> bool {
        use Term::*;
        match self {
            Constant(_) => true,
            Variable(_) => false,
            Function(f) => f.is_ground(),
            Pool(p) => p.is_ground(),
            UnaryOperation(_op, x) => x.is_ground(),
            BinaryOperation(x, _op, y) => x.is_ground() && y.is_ground(),
        }
    }

    fn ground_with(self, bindings: &Bindings) -> Result<Self::Ground, Self::Error> {
        use Term::*;
        match self {
            Constant(c) => Ok(GroundTerm::constant(Value::Constant(c))),
            Variable(name) => Ok(GroundTerm::constant(bindings[&name].clone())),
            Function(f) => Ok(GroundTerm::constant(Value::Function(
                f.ground_with(bindings)?,
            ))),
            Pool(p) => Ok(GroundTerm::Pool(p.ground_with(bindings)?)),
            UnaryOperation(op, x) => Ok(GroundTerm::unary_operation(op, x.ground_with(bindings)?)),
            BinaryOperation(x, op, y) => Ok(GroundTerm::binary_operation(
                x.ground_with(bindings)?,
                op,
                y.ground_with(bindings)?,
            )),
        }
    }

    fn constants(&self, universe: &mut Universe) {
        use Term::*;
        match self {
            Constant(c) => universe.extend([Value::Constant(c.clone())]),
            Function(f) => f.constants(universe),
            Pool(p) => p.constants(universe),
            Variable(..) | BinaryOperation(..) | UnaryOperation(..) => (),
        }
    }

    fn variables(&self, names: &mut Names) {
        if let Term::Variable(v) = self {
            names.insert(v.clone());
        }
    }

    fn functions(&self, functions: &mut Functions) {
        use Term::*;
        match self {
            Function(f) => functions.extend([f.clone()]),
            Pool(p) => p.functions(functions),
            Constant(..) | Variable(..) | BinaryOperation(..) | UnaryOperation(..) => (),
        }
    }
}

impl Groundable for Pool<Term> {
    type Ground = Pool<GroundTerm>;
    type Error = GroundingError;

    fn is_ground(&self) -> bool {
        use Pool::*;
        match self {
            Interval(start, end) => start.is_ground() && end.is_ground(),
            Set(terms) => terms.iter().all(|t| t.is_ground()),
        }
    }

    fn ground_with(self, bindings: &Bindings) -> Result<Self::Ground, Self::Error> {
        use Pool::*;
        match self {
            Interval(start, end) => Ok(Self::Ground::interval(
                start.ground_with(bindings)?,
                end.ground_with(bindings)?,
            )),
            Set(terms) => Ok(Self::Ground::Set(
                terms
                    .into_iter()
                    .map(|t| t.ground_with(bindings))
                    .collect::<Result<_, _>>()?,
            )),
        }
    }

    fn constants(&self, universe: &mut Universe) {
        use Pool::*;
        match self {
            Interval(i, j) if i.is_ground() && j.is_ground() => {
                universe.extend(self.clone().ground().expect("ungrounded interval").values())
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

    fn functions(&self, functions: &mut Functions) {
        use Pool::*;
        match self {
            Interval(start, end) => {
                start.functions(functions);
                end.functions(functions);
            }
            Set(terms) => {
                for term in terms {
                    term.functions(functions);
                }
            }
        }
    }
}

/// Auxiliary atoms are already ground.
impl Groundable for Auxiliary {
    type Ground = Auxiliary;
    type Error = GroundingError;

    fn is_ground(&self) -> bool {
        true
    }
    fn ground_with(self, _: &Bindings) -> Result<Self::Ground, Self::Error> {
        Ok(self)
    }
    fn constants(&self, _: &mut Universe) {}
    fn variables(&self, _: &mut Names) {}
    fn functions(&self, _: &mut Functions) {}
}

impl Groundable for Aggregate<Term> {
    type Ground = Aggregate<GroundTerm>;
    type Error = GroundingError;

    /// An aggregate is ground if all of its choices are ground.
    fn is_ground(&self) -> bool {
        self.choices.iter().all(|choice| choice.is_ground())
    }

    fn ground_with(self, bindings: &Bindings) -> Result<Self::Ground, Self::Error> {
        let Aggregate { choices, bounds } = self;
        Ok(Self::Ground {
            choices: choices
                .into_iter()
                .map(|choice| choice.ground_with(bindings))
                .collect::<Result<_, _>>()?,
            bounds: bounds
                .map(
                    |AggregateBounds {
                         lower_bound,
                         upper_bound,
                     }| {
                        Ok(AggregateBounds::new(
                            lower_bound.ground_with(bindings)?,
                            upper_bound.ground_with(bindings)?,
                        ))
                    },
                )
                .transpose()?,
        })
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

    fn functions(&self, functions: &mut Functions) {
        for choice in &self.choices {
            choice.functions(functions);
        }
    }
}

impl Groundable for Application<Term> {
    type Ground = Application<GroundTerm>;
    type Error = GroundingError;

    /// A predicate application is ground if all of its arguments are ground.
    /// An arity 0 predicate is therefore always ground.
    fn is_ground(&self) -> bool {
        self.arguments.iter().all(|arg| arg.is_ground())
    }

    fn ground_with(self, bindings: &Bindings) -> Result<Self::Ground, Self::Error> {
        Ok(Self::Ground {
            predicate: self.predicate,
            arguments: self
                .arguments
                .into_iter()
                .map(|arg| arg.ground_with(bindings))
                .collect::<Result<_, _>>()?,
        })
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

    fn functions(&self, functions: &mut Functions) {
        for arg in &self.arguments {
            arg.functions(functions);
        }
    }
}

impl Groundable for Atom<Term> {
    type Ground = Atom<GroundTerm>;
    type Error = GroundingError;

    fn is_ground(&self) -> bool {
        use Atom::*;
        match self {
            Aux(..) => true,
            Agg(agg) => agg.is_ground(),
            App(app) => app.is_ground(),
        }
    }

    fn ground_with(self, bindings: &Bindings) -> Result<Self::Ground, Self::Error> {
        use Atom::*;
        match self {
            Aux(aux) => Ok(Self::Ground::Aux(aux.ground_with(bindings)?)),
            Agg(agg) => Ok(Self::Ground::Agg(agg.ground_with(bindings)?)),
            App(app) => Ok(Self::Ground::App(app.ground_with(bindings)?)),
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

    fn functions(&self, functions: &mut Functions) {
        use Atom::*;
        match self {
            Aux(aux) => aux.functions(functions),
            Agg(agg) => agg.functions(functions),
            App(app) => app.functions(functions),
        }
    }
}

impl Groundable for Literal<Term> {
    type Ground = Literal<GroundTerm>;
    type Error = GroundingError;

    fn is_ground(&self) -> bool {
        use Literal::*;
        match self {
            Positive(a) | Negative(a) | DoubleNegative(a) => a.is_ground(),
            Relation(x, _rel, y) => x.is_ground() && y.is_ground(),
        }
    }

    fn ground_with(self, bindings: &Bindings) -> Result<Self::Ground, Self::Error> {
        use Literal::*;
        match self {
            Positive(a) => Ok(Positive(a.ground_with(bindings)?)),
            Negative(a) => Ok(Negative(a.ground_with(bindings)?)),
            DoubleNegative(a) => Ok(DoubleNegative(a.ground_with(bindings)?)),
            Relation(x, rel, y) => Ok(Literal::relation(
                x.ground_with(bindings)?,
                rel,
                y.ground_with(bindings)?,
            )),
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

    fn functions(&self, functions: &mut Functions) {
        use Literal::*;
        match self {
            Positive(a) | Negative(a) | DoubleNegative(a) => a.functions(functions),
            Relation(x, _rel, y) => {
                x.functions(functions);
                y.functions(functions);
            }
        }
    }
}

impl Groundable for BaseProgram {
    type Ground = GroundProgram;
    type Error = GroundingError;

    fn is_ground(&self) -> bool {
        self.iter().all(|rule| rule.is_ground())
    }

    /// Ground with the default grounder.
    fn ground_with(self, bindings: &Bindings) -> Result<Self::Ground, Self::Error> {
        ExhaustiveGrounder::new(self).ground(bindings)
    }

    fn constants(&self, universe: &mut Universe) {
        for rule in self.iter() {
            rule.constants(universe);
        }
    }

    fn variables(&self, names: &mut Names) {
        for rule in self.iter() {
            rule.variables(names);
        }
    }

    fn functions(&self, functions: &mut Functions) {
        for rule in self.iter() {
            rule.functions(functions);
        }
    }
}

impl Groundable for BaseRule<Term> {
    type Ground = BaseRule<GroundTerm>;
    type Error = GroundingError;

    fn is_ground(&self) -> bool {
        match self {
            Self::Choice(rule) => rule.is_ground(),
            Self::Disjunctive(rule) => rule.is_ground(),
        }
    }

    fn ground_with(self, bindings: &Bindings) -> Result<Self::Ground, Self::Error> {
        match self {
            Self::Choice(rule) => Ok(Self::Ground::Choice(rule.ground_with(bindings)?)),
            Self::Disjunctive(rule) => Ok(Self::Ground::Disjunctive(rule.ground_with(bindings)?)),
        }
    }

    fn constants(&self, universe: &mut Universe) {
        match self {
            Self::Choice(rule) => rule.constants(universe),
            Self::Disjunctive(rule) => rule.constants(universe),
        }
    }

    fn variables(&self, names: &mut Names) {
        match self {
            Self::Choice(rule) => rule.variables(names),
            Self::Disjunctive(rule) => rule.variables(names),
        }
    }

    fn functions(&self, functions: &mut Functions) {
        match self {
            Self::Choice(rule) => rule.functions(functions),
            Self::Disjunctive(rule) => rule.functions(functions),
        }
    }
}

impl Groundable for ChoiceRule<Term> {
    type Ground = ChoiceRule<GroundTerm>;
    type Error = GroundingError;

    fn is_ground(&self) -> bool {
        self.head.is_ground() && self.body.iter().all(|b| b.is_ground())
    }

    fn ground_with(self, bindings: &Bindings) -> Result<Self::Ground, Self::Error> {
        Ok(Self::Ground {
            head: self.head.ground_with(bindings)?,
            body: self
                .body
                .into_iter()
                .map(|b| b.ground_with(bindings))
                .collect::<Result<_, _>>()?,
        })
    }

    fn constants(&self, universe: &mut Universe) {
        self.head.constants(universe);
        for b in &self.body {
            b.constants(universe);
        }
    }

    fn variables(&self, names: &mut Names) {
        self.head.variables(names);
        for b in &self.body {
            b.variables(names);
        }
    }

    fn functions(&self, functions: &mut Functions) {
        self.head.functions(functions);
        for b in &self.body {
            b.functions(functions);
        }
    }
}

impl Groundable for Rule<Term> {
    type Ground = Rule<GroundTerm>;
    type Error = GroundingError;

    fn is_ground(&self) -> bool {
        self.head.iter().all(|h| h.is_ground()) && self.body.iter().all(|b| b.is_ground())
    }

    fn ground_with(self, bindings: &Bindings) -> Result<Self::Ground, Self::Error> {
        Ok(Self::Ground {
            head: self
                .head
                .into_iter()
                .map(|h| h.ground_with(bindings))
                .collect::<Result<_, _>>()?,
            body: self
                .body
                .into_iter()
                .map(|b| b.ground_with(bindings))
                .collect::<Result<_, _>>()?,
        })
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

    fn functions(&self, functions: &mut Functions) {
        for h in &self.head {
            h.functions(functions);
        }
        for b in &self.body {
            b.functions(functions);
        }
    }
}
