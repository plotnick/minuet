//! Replace terms that can contain variables with _ground_
//! (variable-free) terms.

#![allow(unused_imports)]

mod exhaustive;
mod groundable;
mod grounder;
mod iterative;
mod term;

use std::collections::{BTreeMap, BTreeSet};
use thiserror::Error;

use minuet_syntax::*;

use crate::values::Value;

// Re-exports.
pub(crate) use exhaustive::ExhaustiveGrounder;
pub use groundable::Groundable;
pub use grounder::Grounder;
pub use term::GroundTerm;

/// Map variable names to constant values (in order to ground them).
pub type Bindings = BTreeMap<Symbol, Value>;

/// A set of variable names (to ground).
pub type Names = BTreeSet<Symbol>;

/// The _Herbrand Universe_ is the set of constant values in a program.
/// It is the set of values to which variables may be bound.
pub type Universe = BTreeSet<Value>;

/// Ungrounded symbolic functions (see "ASP" § 6.6).
pub type Functions = BTreeSet<Application<Term>>;

/// Things that may go wrong during grounding.
#[derive(Clone, Debug, Error)]
#[error("Unable to ground")]
pub enum GroundingError {}

#[cfg(test)]
mod test {
    /// Test helper macro.
    #[macro_export]
    macro_rules! ground {
        ($e: expr) => {
            $e.ground().expect("can't ground test element")
        };
    }
}
