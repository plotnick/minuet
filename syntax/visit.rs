//! Walk a syntax tree, i.e., visit every sub-element.

use super::*;

/// Walk a shared borrow of a syntactic element.
///
/// We follow [the standard Rust visitor
/// pattern](https://rust-unofficial.github.io/patterns/patterns/behavioural/visitor.html).
/// The methods in this trait are hooks to be overridden.
/// By default, they all call out to walker functions that
/// in turn call back into the visitor to continue the walk.
pub trait Visit<'a> {
    fn visit_constant(&mut self, _c: &'a Constant) {}
    fn visit_variable(&mut self, _s: &'a Symbol) {}
    fn visit_predicate_name(&mut self, _p: &'a Symbol) {}
    fn visit_function_name(&mut self, _f: &'a Symbol) {}
    fn visit_pool(&mut self, p: &'a Pool<Term>) {
        visit_pool(self, p)
    }
    fn visit_term(&mut self, t: &'a Term) {
        visit_term(self, t)
    }
    fn visit_function(&mut self, f: &'a Application<Term>) {
        visit_function(self, f)
    }
    fn visit_unary_operation(&mut self, op: UnaryOp, t: &'a Term) {
        visit_unary_operation(self, op, t)
    }
    fn visit_binary_operation(&mut self, l: &'a Term, op: BinOp, r: &'a Term) {
        visit_binary_operation(self, l, op, r)
    }
    fn visit_relation(&mut self, l: &'a Term, op: RelOp, r: &'a Term) {
        visit_relation(self, l, op, r)
    }
    fn visit_head_aggregate(&mut self, a: &'a Aggregate<Term>) {
        visit_head_aggregate(self, a)
    }
    fn visit_body_aggregate(&mut self, a: &'a Aggregate<Term>) {
        visit_body_aggregate(self, a)
    }
    fn visit_aggregate_bounds(&mut self, b: &'a AggregateBounds<Term>) {
        visit_aggregate_bounds(self, b)
    }
    fn visit_head_atom(&mut self, a: &'a Atom<Term>) {
        visit_head_atom(self, a)
    }
    fn visit_body_atom(&mut self, a: &'a Atom<Term>) {
        visit_body_atom(self, a)
    }
    fn visit_head_literal(&mut self, l: &'a Literal<Term>) {
        visit_head_literal(self, l)
    }
    fn visit_body_literal(&mut self, l: &'a Literal<Term>) {
        visit_body_literal(self, l)
    }
    fn visit_base_rule(&mut self, r: &'a BaseRule<Term>) {
        visit_base_rule(self, r)
    }
    fn visit_choice_rule(&mut self, c: &'a ChoiceRule<Term>) {
        visit_choice_rule(self, c)
    }
    fn visit_disjunctive_rule(&mut self, r: &'a Rule<Term>) {
        visit_disjunctive_rule(self, r)
    }
}

pub fn visit_pool<'a, V: Visit<'a> + ?Sized>(v: &mut V, pool: &'a Pool<Term>) {
    match pool {
        Pool::Interval(start, end) => {
            v.visit_term(start);
            v.visit_term(end);
        }
        Pool::Set(elts) => {
            for elt in elts {
                v.visit_term(elt);
            }
        }
    }
}

pub fn visit_term<'a, V: Visit<'a> + ?Sized>(v: &mut V, t: &'a Term) {
    match t {
        Term::Constant(c) => v.visit_constant(c),
        Term::Variable(s) => v.visit_variable(s),
        Term::Function(f) => v.visit_function(f),
        Term::Pool(p) => v.visit_pool(p),
        Term::UnaryOperation(op, t) => v.visit_unary_operation(*op, t),
        Term::BinaryOperation(l, op, r) => v.visit_binary_operation(l, *op, r),
    }
}

pub fn visit_unary_operation<'a, V: Visit<'a> + ?Sized>(v: &mut V, _op: UnaryOp, t: &'a Term) {
    v.visit_term(t);
}

pub fn visit_binary_operation<'a, V: Visit<'a> + ?Sized>(
    v: &mut V,
    left: &'a Term,
    _op: BinOp,
    right: &'a Term,
) {
    v.visit_term(left);
    v.visit_term(right);
}

pub fn visit_relation<'a, V: Visit<'a> + ?Sized>(
    v: &mut V,
    left: &'a Term,
    _op: RelOp,
    right: &'a Term,
) {
    v.visit_term(left);
    v.visit_term(right);
}

pub fn visit_head_aggregate<'a, V: Visit<'a> + ?Sized>(v: &mut V, aggregate: &'a Aggregate<Term>) {
    for c in &aggregate.choices {
        v.visit_head_literal(c);
    }
    if let Some(b) = &aggregate.bounds {
        v.visit_aggregate_bounds(b);
    }
}

pub fn visit_body_aggregate<'a, V: Visit<'a> + ?Sized>(v: &mut V, aggregate: &'a Aggregate<Term>) {
    for c in &aggregate.choices {
        v.visit_body_literal(c);
    }
    if let Some(b) = &aggregate.bounds {
        v.visit_aggregate_bounds(b);
    }
}

pub fn visit_aggregate_bounds<'a, V: Visit<'a> + ?Sized>(
    v: &mut V,
    bounds: &'a AggregateBounds<Term>,
) {
    v.visit_term(&bounds.lower_bound);
    v.visit_term(&bounds.upper_bound);
}

pub fn visit_function<'a, V: Visit<'a> + ?Sized>(v: &mut V, function: &'a Application<Term>) {
    v.visit_function_name(&function.predicate);
    for arg in &function.arguments {
        v.visit_term(arg);
    }
}

pub fn visit_head_atom<'a, V: Visit<'a> + ?Sized>(v: &mut V, atom: &'a Atom<Term>) {
    match atom {
        Atom::Aux(_) => panic!("can't visit an auxiliary"),
        Atom::Agg(a) => v.visit_head_aggregate(a),
        Atom::App(a) => {
            v.visit_predicate_name(&a.predicate);
            for arg in &a.arguments {
                v.visit_term(arg);
            }
        }
    }
}

pub fn visit_body_atom<'a, V: Visit<'a> + ?Sized>(v: &mut V, atom: &'a Atom<Term>) {
    match atom {
        Atom::Aux(_) => panic!("can't visit an auxiliary"),
        Atom::Agg(a) => v.visit_body_aggregate(a),
        Atom::App(a) => {
            v.visit_predicate_name(&a.predicate);
            for arg in &a.arguments {
                v.visit_term(arg);
            }
        }
    }
}

pub fn visit_head_literal<'a, V: Visit<'a> + ?Sized>(v: &mut V, literal: &'a Literal<Term>) {
    match literal {
        Literal::Positive(a) | Literal::Negative(a) | Literal::DoubleNegative(a) => {
            v.visit_head_atom(a)
        }
        Literal::Relation(l, op, r) => v.visit_relation(l, *op, r),
    }
}

pub fn visit_body_literal<'a, V: Visit<'a> + ?Sized>(v: &mut V, literal: &'a Literal<Term>) {
    match literal {
        Literal::Positive(a) | Literal::Negative(a) | Literal::DoubleNegative(a) => {
            v.visit_body_atom(a)
        }
        Literal::Relation(l, op, r) => v.visit_relation(l, *op, r),
    }
}

pub fn visit_base_rule<'a, V: Visit<'a> + ?Sized>(v: &mut V, rule: &'a BaseRule<Term>) {
    match rule {
        BaseRule::Choice(c) => v.visit_choice_rule(c),
        BaseRule::Disjunctive(r) => v.visit_disjunctive_rule(r),
    }
}

pub fn visit_choice_rule<'a, V: Visit<'a> + ?Sized>(v: &mut V, rule: &'a ChoiceRule<Term>) {
    v.visit_head_aggregate(&rule.head);
    for b in &rule.body {
        v.visit_body_literal(b);
    }
}

pub fn visit_disjunctive_rule<'a, V: Visit<'a> + ?Sized>(v: &mut V, rule: &'a Rule<Term>) {
    for l in &rule.head {
        v.visit_head_literal(l);
    }
    for b in &rule.body {
        v.visit_body_literal(b);
    }
}
