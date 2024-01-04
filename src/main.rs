mod builder;
mod solver;
mod domain;

use builder::XccBuilder;
use solver::{print_solutions, XccError};

fn main() -> Result<(), XccError<String, String>> {
    let xcc = XccBuilder::new();
    print_solutions(xcc.build()?.solve()?);
    Ok(())
}
