//! ASP-Core-2 lexer & parser.

pub mod lexer;
pub mod parser;

pub use lexer::{AspCore2Lexer, AspCore2Token};
pub use parser::AspCore2Parser;
