//! Collectors of constants and variables, implemented as
//! [visitors](Visit).

use minuet_syntax::*;

use crate::program::BaseProgram;
use crate::values::Values as _;

use super::{Groundable, Names, Universe, Value};

/// Collect all of the constant values occuring in an element.
pub trait Constants {
    fn constants(&self) -> impl IntoIterator<Item = Value>;
}

impl Constants for BaseProgram {
    fn constants(&self) -> impl IntoIterator<Item = Value> {
        let mut collector = ConstantCollector::default();
        for rule in self.iter() {
            collector.visit_base_rule(rule);
        }
        collector.0.into_iter()
    }
}

#[derive(Default)]
struct ConstantCollector(Universe);

impl<'a> Visit<'a> for ConstantCollector {
    fn visit_constant(&mut self, c: &'a Constant) {
        self.0.insert(Value::Constant(c.clone()));
    }

    fn visit_pool(&mut self, p: &'a Pool<Term>) {
        match p {
            Pool::Interval(start, end) if start.is_ground() && end.is_ground() => self
                .0
                .extend(p.clone().ground().expect("ungrounded interval").values()),
            Pool::Interval(start, end) => {
                todo!("insufficiently instantiated interval {start}..{end}")
            }
            Pool::Set(elts) => {
                for elt in elts {
                    visit_term(self, elt);
                }
            }
        }
    }
}

/// Collect all of the variables occuring in an element.
pub trait Variables {
    fn variables(&self) -> impl IntoIterator<Item = Symbol>;
}

impl Variables for BaseRule<Term> {
    fn variables(&self) -> impl IntoIterator<Item = Symbol> {
        let mut collector = VariableCollector::default();
        collector.visit_base_rule(self);
        collector.0.into_iter()
    }
}

impl Variables for BaseProgram {
    fn variables(&self) -> impl IntoIterator<Item = Symbol> {
        let mut collector = VariableCollector::default();
        for rule in self.iter() {
            collector.visit_base_rule(rule);
        }
        collector.0.into_iter()
    }
}

#[derive(Default)]
struct VariableCollector(Names);

impl<'a> Visit<'a> for VariableCollector {
    fn visit_variable(&mut self, s: &'a Symbol) {
        self.0.insert(s.clone());
    }
}

/// Search for a (or any) variable.
pub trait ContainsVariable {
    fn contains_variable(&self, variable: Option<&Symbol>) -> bool;
}

impl ContainsVariable for Literal<Term> {
    fn contains_variable(&self, variable: Option<&Symbol>) -> bool {
        let mut visitor = ContainsVariableVisitor::new(variable);
        visitor.visit_body_literal(self);
        visitor.found
    }
}

struct ContainsVariableVisitor<'v> {
    variable: Option<&'v Symbol>,
    found: bool,
}

impl<'v> ContainsVariableVisitor<'v> {
    fn new(variable: Option<&'v Symbol>) -> Self {
        Self {
            variable,
            found: false,
        }
    }
}

impl<'a, 'v> Visit<'a> for ContainsVariableVisitor<'v> {
    fn visit_variable(&mut self, s: &'a Symbol) {
        if self.variable.map(|v| v == s).unwrap_or(true) {
            self.found = true;
        }
    }
}

/// Determine if an element is variable-free.
pub trait IsGround {
    fn is_ground(&self) -> bool;
}

impl IsGround for Term {
    fn is_ground(&self) -> bool {
        let mut visitor = ContainsVariableVisitor::new(None);
        visitor.visit_term(self);
        !visitor.found
    }
}

impl IsGround for BaseRule<Term> {
    fn is_ground(&self) -> bool {
        let mut visitor = ContainsVariableVisitor::new(None);
        visitor.visit_base_rule(self);
        !visitor.found
    }
}
