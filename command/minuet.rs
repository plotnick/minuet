use std::fs::read_to_string;
use std::io::{stdin, Read};

use anyhow::{anyhow, Context as _, Result};

use minuet_semantics::XccCompiler;
use minuet_syntax::{Lex as _, Minuet1Lexer, Minuet1Parser, Parse as _, Tokens};
use minuet_tracer::Trace;

fn main() -> Result<()> {
    let input = read_file(None)?;
    let (_, tokens) = Minuet1Lexer::lex(&input).map_err(|e| anyhow!(e.to_string()))?;
    let (_, rules) =
        Minuet1Parser::parse(Tokens::new(&tokens[..])).map_err(|e| anyhow!(e.to_string()))?;
    let xcc = XccCompiler::new(rules, Trace::all()).unwrap();
    let _solutions = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
    Ok(())
}

/// Read a file or standard input and return the content as a string.
fn read_file(filename: Option<&str>) -> Result<String> {
    match filename {
        None | Some("-") => {
            let mut buffer = String::new();
            stdin()
                .read_to_string(&mut buffer)
                .context("Reading from stdin")?;
            Ok(buffer)
        }
        Some(filename) => read_to_string(filename).with_context(|| format!("Reading {filename}")),
    }
}
