mod builder;
mod domain;
mod solver;

#[macro_use]
mod syntax;
mod formula;
mod semantics;
mod compiler;

use builder::XccBuilder;
use solver::XccError;

fn main() -> Result<(), XccError<String, String>> {
    let mut builder = XccBuilder::new();
    builder.trace(true).unwrap();
    let xcc = builder.build()?;
    let _solutions = xcc.solve().collect::<Result<Vec<_>, _>>().unwrap();
    Ok(())
}
