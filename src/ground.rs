//! Replace terms that can contain variables with _ground_
//! (variable-free) terms.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::generate::combinations_mixed;
use crate::semantics::Program;
use crate::syntax::*;
use crate::values::Values as _;

/// Map variable names to constant values (in order to ground them).
pub type Bindings = BTreeMap<Symbol, Constant>;

/// A set of variable names (to ground).
pub type Names = BTreeSet<Symbol>;

/// The _Herbrand Universe_ is the set of all constants in a program.
/// It is the set of values to which variables may be bound.
pub type Universe = BTreeSet<Constant>;

/// Terms that can contain variables may be _grounded_, wherein we replace
/// all variables with all possible values that can be bound to them.
///
/// The `Ground` associated type represents the _result_ of the grounding,
/// e.g., we go from `Rule<Term>` → `Rule<GroundTerm>` via:
/// ```
/// impl Groundable for Rule<Term> {
///     type Ground = Rule<GroundTerm>;
///     ...
/// }
/// ```
pub trait Groundable {
    type Ground;

    fn is_ground(&self) -> bool;
    fn ground_with(self, bindings: &Bindings) -> Self::Ground;
    fn ground(self) -> Self::Ground
    where
        Self: Sized,
    {
        self.ground_with(&Bindings::new())
    }
    fn constants(&self, universe: &mut Universe);
    fn variables(&self, names: &mut Names);
}

/// Ground (variable-free) element that represents a fixed set of values.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum GroundTerm {
    Constant(Constant),
    Choice(Pool<GroundTerm>),
    UnaryOperation(UnaryOp, Box<GroundTerm>),
    BinaryOperation(Box<GroundTerm>, BinOp, Box<GroundTerm>),
}

impl GroundTerm {
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
        Self::Constant(c)
    }
}

impl fmt::Display for GroundTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use GroundTerm::*;
        use UnaryOp::*;
        match self {
            Constant(x) => x.fmt(f),
            Choice(x) => x.fmt(f),
            UnaryOperation(Abs, x) => f.write_fmt(format_args!("|{x}|")),
            UnaryOperation(Neg, x) => f.write_fmt(format_args!("-{x}")),
            UnaryOperation(Not, x) => f.write_fmt(format_args!("~{x}")),
            BinaryOperation(x, op, y) => f.write_fmt(format_args!("{x} {op} {y}")),
        }
    }
}

impl Groundable for Term {
    type Ground = GroundTerm;

    fn is_ground(&self) -> bool {
        use Term::*;
        match self {
            Constant(_) => true,
            Variable(_) => false,
            Choice(p) => p.is_ground(),
            UnaryOperation(_op, x) => x.is_ground(),
            BinaryOperation(x, _op, y) => x.is_ground() && y.is_ground(),
        }
    }

    fn ground_with(self, bindings: &Bindings) -> GroundTerm {
        match self {
            Term::Constant(c) => GroundTerm::Constant(c),
            Term::Choice(p) => GroundTerm::Choice(p.ground_with(bindings)),
            Term::Variable(name) => GroundTerm::Constant(bindings[&name].clone()),
            Term::UnaryOperation(op, x) => GroundTerm::unary_operation(op, x.ground_with(bindings)),
            Term::BinaryOperation(x, op, y) => {
                GroundTerm::binary_operation(x.ground_with(bindings), op, y.ground_with(bindings))
            }
        }
    }

    fn constants(&self, universe: &mut Universe) {
        use Term::*;
        match self {
            Constant(c) => universe.extend([c.clone()]),
            Choice(c) => c.constants(universe),
            Variable(..) | BinaryOperation(..) | UnaryOperation(..) => (),
        }
    }

    fn variables(&self, names: &mut Names) {
        if let Term::Variable(v) = self {
            names.insert(v.clone());
        }
    }
}

impl Groundable for Pool<Term> {
    type Ground = Pool<GroundTerm>;

    fn is_ground(&self) -> bool {
        use Pool::*;
        match self {
            Interval(start, end) => start.is_ground() && end.is_ground(),
            Set(terms) => terms.iter().all(|t| t.is_ground()),
        }
    }

    fn ground_with(self, bindings: &Bindings) -> Self::Ground {
        use Pool::*;
        match self {
            Interval(start, end) => {
                Self::Ground::interval(start.ground_with(bindings), end.ground_with(bindings))
            }
            Set(terms) => Self::Ground::set(terms.into_iter().map(|t| t.ground_with(bindings))),
        }
    }

    fn constants(&self, universe: &mut Universe) {
        use Pool::*;
        match self {
            Interval(i, j) if i.is_ground() && j.is_ground() => {
                universe.extend(self.clone().ground().values())
            }
            Interval(i, j) => todo!("insufficiently instantiated interval {i}..{j}"),
            Set(terms) => {
                for term in terms {
                    term.constants(universe);
                }
            }
        }
    }

    fn variables(&self, names: &mut Names) {
        use Pool::*;
        match self {
            Interval(start, end) => {
                start.variables(names);
                end.variables(names);
            }
            Set(terms) => {
                for term in terms {
                    term.variables(names);
                }
            }
        }
    }
}

/// Auxiliary atoms are already ground.
impl Groundable for Auxiliary {
    type Ground = Auxiliary;

    fn is_ground(&self) -> bool {
        true
    }
    fn ground_with(self, _: &Bindings) -> Self::Ground {
        self
    }
    fn constants(&self, _: &mut Universe) {}
    fn variables(&self, _: &mut Names) {}
}

impl Groundable for Aggregate<Term> {
    type Ground = Aggregate<GroundTerm>;

    /// An aggregate is ground if all of its choices are ground.
    fn is_ground(&self) -> bool {
        self.choices.iter().all(|choice| choice.is_ground())
    }

    fn ground_with(self, bindings: &Bindings) -> Self::Ground {
        let Aggregate { choices, bounds } = self;
        Self::Ground {
            choices: choices
                .into_iter()
                .map(|choice| choice.ground_with(bindings))
                .collect(),
            bounds: bounds.map(
                |AggregateBounds {
                     lower_bound,
                     upper_bound,
                 }| {
                    AggregateBounds::new(
                        lower_bound.ground_with(bindings),
                        upper_bound.ground_with(bindings),
                    )
                },
            ),
        }
    }

    fn constants(&self, universe: &mut Universe) {
        for choice in &self.choices {
            choice.constants(universe);
        }
    }

    fn variables(&self, names: &mut Names) {
        for choice in &self.choices {
            choice.variables(names);
        }
    }
}

impl Groundable for Application<Term> {
    type Ground = Application<GroundTerm>;

    /// A predicate application is ground if all of its arguments are ground.
    /// An arity 0 predicate is therefore always ground.
    fn is_ground(&self) -> bool {
        self.arguments.iter().all(|arg| arg.is_ground())
    }

    fn ground_with(self, bindings: &Bindings) -> Self::Ground {
        Self::Ground {
            predicate: self.predicate,
            arguments: self
                .arguments
                .into_iter()
                .map(|arg| arg.ground_with(bindings))
                .collect(),
        }
    }

    fn constants(&self, universe: &mut Universe) {
        for arg in &self.arguments {
            arg.constants(universe);
        }
    }

    fn variables(&self, names: &mut Names) {
        for arg in &self.arguments {
            arg.variables(names);
        }
    }
}

impl Groundable for Atom<Term> {
    type Ground = Atom<GroundTerm>;

    fn is_ground(&self) -> bool {
        use Atom::*;
        match self {
            Aux(..) => true,
            Agg(agg) => agg.is_ground(),
            App(app) => app.is_ground(),
        }
    }

    fn ground_with(self, bindings: &Bindings) -> Self::Ground {
        use Atom::*;
        match self {
            Aux(aux) => Self::Ground::Aux(aux.ground_with(bindings)),
            Agg(agg) => Self::Ground::Agg(agg.ground_with(bindings)),
            App(app) => Self::Ground::App(app.ground_with(bindings)),
        }
    }

    fn constants(&self, universe: &mut Universe) {
        use Atom::*;
        match self {
            Aux(aux) => aux.constants(universe),
            Agg(agg) => agg.constants(universe),
            App(app) => app.constants(universe),
        }
    }

    fn variables(&self, names: &mut Names) {
        use Atom::*;
        match self {
            Aux(aux) => aux.variables(names),
            Agg(agg) => agg.variables(names),
            App(app) => app.variables(names),
        }
    }
}

impl Groundable for Literal<Term> {
    type Ground = Literal<GroundTerm>;

    fn is_ground(&self) -> bool {
        use Literal::*;
        match self {
            Positive(a) | Negative(a) | DoubleNegative(a) => a.is_ground(),
            Relation(x, _rel, y) => x.is_ground() && y.is_ground(),
        }
    }

    fn ground_with(self, bindings: &Bindings) -> Self::Ground {
        use Literal::*;
        match self {
            Positive(a) => Positive(a.ground_with(bindings)),
            Negative(a) => Negative(a.ground_with(bindings)),
            DoubleNegative(a) => DoubleNegative(a.ground_with(bindings)),
            Relation(x, rel, y) => {
                Literal::relation(x.ground_with(bindings), rel, y.ground_with(bindings))
            }
        }
    }

    fn constants(&self, universe: &mut Universe) {
        use Literal::*;
        match self {
            Positive(a) | Negative(a) | DoubleNegative(a) => a.constants(universe),
            Relation(x, _rel, y) => {
                x.constants(universe);
                y.constants(universe);
            }
        }
    }

    fn variables(&self, names: &mut Names) {
        use Literal::*;
        match self {
            Positive(a) | Negative(a) | DoubleNegative(a) => a.variables(names),
            Relation(x, _rel, y) => {
                x.variables(names);
                y.variables(names);
            }
        }
    }
}

impl Groundable for Program<BaseRule<Term>> {
    type Ground = Program<BaseRule<GroundTerm>>;

    fn is_ground(&self) -> bool {
        self.iter().all(|rule| rule.is_ground())
    }

    /// Find all constants and bind all variables to them in all possible ways.
    /// TODO: less naïve grounding strategy, inject initial bindings.
    fn ground_with(self, _bindings: &Bindings) -> Self::Ground {
        let mut constants = Universe::new();
        self.constants(&mut constants);
        let constants = constants.into_iter().collect::<Vec<Constant>>();

        let mut variables = Names::new();
        self.variables(&mut variables);
        let variables = variables.into_iter().collect::<Vec<Symbol>>();

        let (ground_rules, var_rules): (Vec<_>, Vec<_>) =
            self.into_iter().partition(|r| r.is_ground());
        let mut rules = ground_rules
            .into_iter()
            .map(|rule| rule.ground())
            .collect::<Vec<_>>();

        let m = constants.len();
        let n = variables.len();
        combinations_mixed(n, &vec![m; n], |a: &[usize]| {
            let bindings = a
                .iter()
                .enumerate()
                .map(|(i, &j)| (variables[i].clone(), constants[j].clone()))
                .collect::<Bindings>();
            rules.extend(
                var_rules
                    .iter()
                    .cloned()
                    .map(|rule| rule.ground_with(&bindings)),
            );
        });

        Program::new(rules)
    }

    fn constants(&self, universe: &mut Universe) {
        for rule in self.iter() {
            rule.constants(universe);
        }
    }

    fn variables(&self, names: &mut Names) {
        for rule in self.iter() {
            rule.variables(names);
        }
    }
}

impl Groundable for BaseRule<Term> {
    type Ground = BaseRule<GroundTerm>;

    fn is_ground(&self) -> bool {
        match self {
            Self::Choice(rule) => rule.is_ground(),
            Self::Disjunctive(rule) => rule.is_ground(),
        }
    }

    fn ground_with(self, bindings: &Bindings) -> Self::Ground {
        match self {
            Self::Choice(rule) => Self::Ground::Choice(rule.ground_with(bindings)),
            Self::Disjunctive(rule) => Self::Ground::Disjunctive(rule.ground_with(bindings)),
        }
    }

    fn constants(&self, universe: &mut Universe) {
        match self {
            Self::Choice(rule) => rule.constants(universe),
            Self::Disjunctive(rule) => rule.constants(universe),
        }
    }

    fn variables(&self, names: &mut Names) {
        match self {
            Self::Choice(rule) => rule.variables(names),
            Self::Disjunctive(rule) => rule.variables(names),
        }
    }
}

impl Groundable for ChoiceRule<Term> {
    type Ground = ChoiceRule<GroundTerm>;

    fn is_ground(&self) -> bool {
        self.head.is_ground() && self.body.iter().all(|b| b.is_ground())
    }

    fn ground_with(self, bindings: &Bindings) -> Self::Ground {
        Self::Ground::new(
            self.head.ground_with(bindings),
            self.body.into_iter().map(|b| b.ground_with(bindings)),
        )
    }

    fn constants(&self, universe: &mut Universe) {
        self.head.constants(universe);
        for b in &self.body {
            b.constants(universe);
        }
    }

    fn variables(&self, names: &mut Names) {
        self.head.variables(names);
        for b in &self.body {
            b.variables(names);
        }
    }
}

impl Groundable for Rule<Term> {
    type Ground = Rule<GroundTerm>;

    fn is_ground(&self) -> bool {
        self.head.iter().all(|h| h.is_ground()) && self.body.iter().all(|b| b.is_ground())
    }

    fn ground_with(self, bindings: &Bindings) -> Self::Ground {
        Self::Ground::new(
            self.head.into_iter().map(|h| h.ground_with(bindings)),
            self.body.into_iter().map(|b| b.ground_with(bindings)),
        )
    }

    fn constants(&self, universe: &mut Universe) {
        for h in &self.head {
            h.constants(universe);
        }
        for b in &self.body {
            b.constants(universe);
        }
    }

    fn variables(&self, names: &mut Names) {
        for h in &self.head {
            h.variables(names);
        }
        for b in &self.body {
            b.variables(names);
        }
    }
}
