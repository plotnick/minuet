//! A quite-good strategy for grounding: start with the facts,
//! and iteratively collect bindings.

#![allow(dead_code)]

use minuet_syntax::{BaseRule, Term};

use crate::program::BaseProgram;

use super::{Bindings, Groundable, Grounder};

pub(crate) struct IterativeGrounder {}

impl Grounder<BaseProgram> for IterativeGrounder {
    fn ground(
        self,
        _bindings: &Bindings,
    ) -> Result<<BaseProgram as Groundable>::Ground, <BaseProgram as Groundable>::Error> {
        todo!("start with the facts and work out from there")
    }
}
