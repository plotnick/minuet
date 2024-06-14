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

    /// Perform the bindings in [`Bindings`] and return a grounded
    /// (or more nearly grounded) element. Intended only to be called
    /// by [`Grounder::ground`].
    fn ground_with(self, bindings: &Bindings) -> Result<Self::Ground, Self::Error>;

    /// Convenience method: ground with an empty set of bindings.
    fn ground(self) -> Result<Self::Ground, Self::Error>
    where
        Self: Sized,
    {
        self.ground_with(&Bindings::new())
    }
}

impl Groundable for Term {
    type Ground = GroundTerm;
    type Error = GroundingError;

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
}

impl Groundable for Pool<Term> {
    type Ground = Pool<GroundTerm>;
    type Error = GroundingError;

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
}

/// Auxiliary atoms are already ground.
impl Groundable for Auxiliary {
    type Ground = Auxiliary;
    type Error = GroundingError;

    fn ground_with(self, _: &Bindings) -> Result<Self::Ground, Self::Error> {
        Ok(self)
    }
}

impl Groundable for Aggregate<Term> {
    type Ground = Aggregate<GroundTerm>;
    type Error = GroundingError;

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
}

impl Groundable for Application<Term> {
    type Ground = Application<GroundTerm>;
    type Error = GroundingError;

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
}

impl Groundable for Atom<Term> {
    type Ground = Atom<GroundTerm>;
    type Error = GroundingError;

    fn ground_with(self, bindings: &Bindings) -> Result<Self::Ground, Self::Error> {
        use Atom::*;
        match self {
            Aux(aux) => Ok(Self::Ground::Aux(aux.ground_with(bindings)?)),
            Agg(agg) => Ok(Self::Ground::Agg(agg.ground_with(bindings)?)),
            App(app) => Ok(Self::Ground::App(app.ground_with(bindings)?)),
        }
    }
}

impl Groundable for Literal<Term> {
    type Ground = Literal<GroundTerm>;
    type Error = GroundingError;

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
}

impl Groundable for BaseProgram {
    type Ground = GroundProgram;
    type Error = GroundingError;

    /// Ground with the default grounder.
    fn ground_with(self, bindings: &Bindings) -> Result<Self::Ground, Self::Error> {
        ExhaustiveGrounder::new(self).ground(bindings)
    }
}

impl Groundable for BaseRule<Term> {
    type Ground = BaseRule<GroundTerm>;
    type Error = GroundingError;

    fn ground_with(self, bindings: &Bindings) -> Result<Self::Ground, Self::Error> {
        match self {
            Self::Choice(rule) => Ok(Self::Ground::Choice(rule.ground_with(bindings)?)),
            Self::Disjunctive(rule) => Ok(Self::Ground::Disjunctive(rule.ground_with(bindings)?)),
        }
    }
}

impl Groundable for ChoiceRule<Term> {
    type Ground = ChoiceRule<GroundTerm>;
    type Error = GroundingError;

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
}

impl Groundable for Rule<Term> {
    type Ground = Rule<GroundTerm>;
    type Error = GroundingError;

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
}
