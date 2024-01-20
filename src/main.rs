#[macro_use]
mod syntax;
#[macro_use]
mod tracer;

mod compiler;
mod domain;
mod formula;
mod semantics;
mod solver;

use compiler::{XccCompiler, XccError};

fn main() -> Result<(), XccError<String, String>> {
    let xcc = XccCompiler::new(vec![], true).unwrap();
    let _solutions = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
    Ok(())
}
