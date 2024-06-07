//! Turn a program that contains variables into one that does not.

use super::{Bindings, Groundable};

/// There are many possible ways of grounding: some good,
/// some not so good. This trait allows us to experiment;
/// it makes no judgements of its own.
pub trait Grounder<T: Groundable> {
    /// Ground `self` with respect to some initial `bindings`.
    fn ground(
        self,
        bindings: &Bindings,
    ) -> Result<<T as Groundable>::Ground, <T as Groundable>::Error>;
}
