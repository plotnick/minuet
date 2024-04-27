use minuet_semantics::{XccCompiler, XccError};
use minuet_tracer::Trace;

fn main() -> Result<(), XccError<String, String>> {
    let xcc = XccCompiler::new(vec![], Trace::all()).unwrap();
    let _solutions = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
    Ok(())
}
