//! Meaning-preserving manipulation of logic programs: ground all variables,
//! normalize propositional images, and complete rules by transforming them
//! from implications into equivalences.

mod clause;
mod compiler;
mod formula;
mod generate;
mod ground;
mod image;
mod program;
mod values;

pub use compiler::XccCompiler;
pub use minuet_solver::XccError;
pub use program::Program;
