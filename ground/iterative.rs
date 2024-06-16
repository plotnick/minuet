//! A quite-good strategy for grounding: start with the facts,
//! and iteratively collect bindings.

#![allow(dead_code)]

use minuet_syntax::{BaseRule, Term};

use super::{Bindings, GroundTerm, Groundable, Grounder, GroundingError};

pub(crate) struct IterativeGrounder {}

impl Grounder<Vec<BaseRule<Term>>> for IterativeGrounder {
    fn ground(self, _bindings: &Bindings) -> Result<Vec<BaseRule<GroundTerm>>, GroundingError> {
        todo!("start with the facts and work out from there")
    }
}
