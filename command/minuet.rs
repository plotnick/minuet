//! An interactive interpreter: read a minuet program;
//! parse, compile, and solve it; print the answer sets.

use std::fs::read_to_string;
use std::io::{stdin, Read};

use anyhow::{anyhow, Context as _, Result};
use atty::Stream;

use minuet_semantics::{format_answer, XccCompiler};
use minuet_syntax::{Lex as _, Minuet1Lexer, Minuet1Parser, Parse as _, Tokens};
use minuet_tracer::Trace;

fn main() -> Result<()> {
    if atty::is(Stream::Stdin) && atty::is(Stream::Stdout) {
        println!("Welcome to Minuet! Please enter your rules, terminated with Ctrl-D.");
    }
    let input = read_file(None)?;
    let (_, tokens) = Minuet1Lexer::lex(&input).map_err(|e| anyhow!(e.to_string()))?;
    let (_, rules) =
        Minuet1Parser::parse(Tokens::new(&tokens[..])).map_err(|e| anyhow!(e.to_string()))?;
    let xcc = XccCompiler::new(rules, Trace::all())?;
    for answer in xcc.run().collect::<Result<Vec<_>, _>>()? {
        println!("{}", format_answer(&answer));
    }
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
