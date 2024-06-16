//! Meaning-preserving manipulation of logic programs: ground all variables,
//! normalize propositional images, and complete rules by transforming them
//! from implications into equivalences.

#![allow(rustdoc::private_intra_doc_links)]

mod clause;
mod compiler;
mod formula;
mod image;
mod program;

pub use compiler::XccCompiler;
pub use minuet_solver::XccError;
