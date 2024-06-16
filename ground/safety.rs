//! Check that all (global) variables in a rule are _safe_,
//! i.e., occur in at least one positive body literal.
//!
//! This is totally unrelated to Rust's `unsafe` keyword.

use minuet_syntax::*;

use super::{ContainsVariable, Groundable, GroundingError, Names, Variables};

pub trait Safety<T: Groundable> {
    fn check_safety(&self) -> Result<(), <T as Groundable>::Error>;
}

impl Safety<BaseRule<Term>> for BaseRule<Term> {
    fn check_safety(&self) -> Result<(), GroundingError> {
        for v in self.variables() {
            match self {
                Self::Choice(ChoiceRule { head: _, body })
                | Self::Disjunctive(Rule { head: _, body }) => {
                    if !body.iter().any(|l| {
                        (l.is_positive() || matches!(l, Literal::Relation(_, RelOp::Eq, _)))
                            && l.contains_variable(Some(&v))
                    }) {
                        return Err(GroundingError::UnsafeVariable(v));
                    }
                }
            }
        }
        Ok(())
    }
}
