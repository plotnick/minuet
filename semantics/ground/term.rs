//! Ground version of [`minuet_syntax::Term`].

use std::fmt;

use minuet_syntax::*;

use crate::values::Value;

/// Ground (variable-free) element that represents a fixed set
/// of constant values.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum GroundTerm {
    Constant(Box<Value>),
    Pool(Pool<GroundTerm>),
    UnaryOperation(UnaryOp, Box<GroundTerm>),
    BinaryOperation(Box<GroundTerm>, BinOp, Box<GroundTerm>),
}

impl GroundTerm {
    /// Boxing constructor.
    pub fn constant(v: Value) -> Self {
        Self::Constant(Box::new(v))
    }

    /// Boxing constructor.
    pub fn unary_operation(op: UnaryOp, x: GroundTerm) -> Self {
        Self::UnaryOperation(op, Box::new(x))
    }

    /// Boxing constructor.
    pub fn binary_operation(x: GroundTerm, op: BinOp, y: GroundTerm) -> Self {
        Self::BinaryOperation(Box::new(x), op, Box::new(y))
    }
}

impl From<Constant> for GroundTerm {
    fn from(c: Constant) -> Self {
        Self::constant(Value::Constant(c))
    }
}

impl fmt::Display for GroundTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use GroundTerm::*;
        use UnaryOp::*;
        match self {
            Constant(x) => x.fmt(f),
            Pool(x) => x.fmt(f),
            UnaryOperation(Abs, x) => f.write_fmt(format_args!("|{x}|")),
            UnaryOperation(Neg, x) => f.write_fmt(format_args!("-{x}")),
            UnaryOperation(Not, x) => f.write_fmt(format_args!("~{x}")),
            BinaryOperation(x, op, y) => f.write_fmt(format_args!("{x} {op} {y}")),
        }
    }
}
