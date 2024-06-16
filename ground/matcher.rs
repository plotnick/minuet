//! One-sided unification, i.e., matching of ground terms.

use minuet_syntax::*;

use super::Bindings;

/// Match one element against another, binding variables
/// on the left to elements on the right. Adapted from the
/// `GroundMatch` trait in [mu-gringo](https://github.com/potassco/mu-gringo).
pub trait Matcher {
    fn matches(&self, other: &Self, bindings: &mut Bindings) -> bool;
}

impl Matcher for Term {
    fn matches(&self, other: &Self, bindings: &mut Bindings) -> bool {
        todo!("match {other:?} w/r/t {bindings:?}")
    }
}
