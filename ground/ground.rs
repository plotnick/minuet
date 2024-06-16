//! Replace terms that can contain variables with _ground_
//! (variable-free) terms.

#![allow(unused_imports)]

mod collectors;
mod combinations;
mod exhaustive;
mod groundable;
mod grounder;
mod iterative;
mod safety;
mod term;
mod values;

use std::collections::{BTreeMap, BTreeSet};
use thiserror::Error;

use minuet_syntax::*;

// Re-exports.
pub use collectors::{Constants, ContainsVariable, IsGround, Variables};
pub use combinations::{combinations, combinations_mixed};
pub(crate) use exhaustive::ExhaustiveGrounder;
pub use groundable::Groundable;
pub use grounder::Grounder;
pub use safety::Safety;
pub use term::GroundTerm;
pub use values::{all_values, for_all_value_pairs, Value, ValueSet, Values};

/// Map variable names to constant values (in order to ground them).
pub type Bindings = BTreeMap<Symbol, Value>;

/// A set of variable names (to ground).
pub type Names = BTreeSet<Symbol>;

/// The _Herbrand Universe_ is the set of constant values in a program.
/// It is the set of values to which variables may be bound.
pub type Universe = BTreeSet<Value>;

/// Ungrounded symbolic functions (see "ASP" § 6.6).
#[allow(dead_code)]
pub type Functions = BTreeSet<Application<Term>>;

/// Things that may go wrong during grounding.
#[derive(Clone, Debug, Error)]
#[error("Unable to ground")]
pub enum GroundingError {
    #[error("unsafe variable: `{0}` does not appear in any positive body literal")]
    UnsafeVariable(Symbol),
}

/// Test helper macros.
///
/// This should be behind `#[cfg(test)]`, but [cargo can't
/// currently export test code across crates](https://github.com/rust-lang/cargo/issues/8379).
#[cfg(feature = "macros")]
mod macros {
    /// Ground an element or die trying.
    #[macro_export]
    macro_rules! ground {
        ($e: expr) => {
            $e.ground().expect("can't ground test element")
        };
    }
}
