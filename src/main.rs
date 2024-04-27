mod clause;
mod compiler;
mod domain;
mod formula;
mod generate;
mod ground;
mod id;
mod image;
mod semantics;
mod solver;
mod values;

use minuet_tracer::Trace;

use compiler::{XccCompiler, XccError};

fn main() -> Result<(), XccError<String, String>> {
    let xcc = XccCompiler::new(vec![], Trace::all()).unwrap();
    let _solutions = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
    Ok(())
}
