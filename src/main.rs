#[macro_use]
mod syntax;
#[macro_use]
mod tracer;

mod clause;
mod compiler;
mod domain;
mod formula;
mod generate;
mod image;
mod semantics;
mod solver;
mod values;

use compiler::{XccCompiler, XccError};
use tracer::Trace;

fn main() -> Result<(), XccError<String, String>> {
    let xcc = XccCompiler::new(vec![], Trace::all()).unwrap();
    let _solutions = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
    Ok(())
}
