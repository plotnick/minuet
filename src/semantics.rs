//! Meaning-preserving manipulation of logic programs: ground all variables,
//! remove all disjunctions, and "complete" all rules by transforming them
//! from implications into equivalences. (See Dodaro's dissertation, Lifschitz
//! "ASP", etc.) These are all pre-processing steps prior to compilation into
//! a combinatorial search problem and resolution into stable models.

#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::formula::{Bindings, Formula, Interpretation, Names, Universe};
use crate::syntax::*;

/// A program is a collection of rules that we'll process in strict order,
/// generating a new (potentially much larger) set of rules at each stage:
///
///   Program → Normal Program → Ground Program → Complete Program
///
/// Only the first has a public constructor; the others must be produced
/// by calling the appropriate method (`normalize`, `ground`, `complete`)
/// on their predecessor.
#[derive(Clone, Debug)]
pub struct Program(Vec<Rule>);

impl Program {
    pub fn new(rules: impl IntoIterator<Item = Rule>) -> Self {
        Self(rules.into_iter().collect())
    }

    pub fn iter(&self) -> impl Iterator<Item = &Rule> {
        self.0.iter()
    }

    pub fn into_iter(self) -> impl Iterator<Item = Rule> {
        self.0.into_iter()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn normalize(self) -> NormalProgram {
        NormalProgram::new(self.iter().flat_map(NormalRule::normalize))
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for c in self.iter() {
            c.fmt(f)?;
            f.write_str("\n")?;
        }
        Ok(())
    }
}

/// A "normal" (non-disjunctive, Prolog-style) rule has at most one head atom
/// and a (possibly empty) conjunctive body.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct NormalRule {
    head: Option<Atom>,
    body: Vec<Literal>,
}

impl NormalRule {
    fn new(head: Option<Atom>, body: impl IntoIterator<Item = Literal>) -> Self {
        Self {
            head,
            body: body.into_iter().collect(),
        }
    }

    /// Build a set of normal (non-disjunctive) rules from a disjunctive rule, one
    /// for each atom in the head. Also called rule shifting (Dodaro Definition 10).
    fn normalize(rule: &Rule) -> Vec<Self> {
        if rule.head.is_empty() {
            vec![Self::new(None, rule.body.clone())]
        } else {
            rule.head
                .iter()
                .map(|h| {
                    Self::new(
                        Some(h.clone()),
                        rule.body
                            .iter()
                            .cloned()
                            .chain(rule.head.iter().filter_map(|a| {
                                if a != h {
                                    Some(Literal::Negative(a.clone()))
                                } else {
                                    None
                                }
                            })),
                    )
                })
                .collect::<Vec<_>>()
        }
    }
}

impl Formula for NormalRule {
    fn atoms(&self, interp: &mut Interpretation) {
        for h in &self.head {
            h.atoms(interp);
        }
        for b in &self.body {
            b.atoms(interp);
        }
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

    fn is_definite(&self) -> bool {
        self.head.iter().all(|h| h.is_definite()) && self.body.iter().all(|b| b.is_definite())
    }

    fn is_ground(&self) -> bool {
        self.head.iter().all(|h| h.is_ground()) && self.body.iter().all(|b| b.is_ground())
    }

    fn eval(&self, interp: &Interpretation) -> bool {
        self.head.iter().any(|h| h.eval(interp)) && self.body.iter().all(|b| b.eval(interp))
    }

    fn ground(self, bindings: &Bindings) -> Self {
        Self::new(
            self.head.map(|h| h.ground(bindings)),
            self.body.into_iter().map(|b| b.ground(bindings)),
        )
    }

    fn reduce(self, _interp: &Interpretation) -> Self {
        todo!("reduce normal rule")
    }
}

impl fmt::Display for NormalRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match (&self.head, self.body.is_empty()) {
            (None, true) => Ok(()),
            (None, false) => f.write_fmt(format_args!(
                "if {}",
                self.body
                    .iter()
                    .map(|c| c.to_string())
                    .collect::<Vec<_>>()
                    .join(" and ")
            )),
            (Some(head), true) => f.write_fmt(format_args!("{head}")),
            (Some(head), false) => f.write_fmt(format_args!(
                "{head} if {}",
                self.body
                    .iter()
                    .map(|c| c.to_string())
                    .collect::<Vec<_>>()
                    .join(" and ")
            )),
        }
    }
}

#[derive(Clone, Debug)]
pub struct NormalProgram(Vec<NormalRule>);

impl NormalProgram {
    fn new(rules: impl IntoIterator<Item = NormalRule>) -> Self {
        Self(rules.into_iter().collect())
    }

    pub fn iter(&self) -> impl Iterator<Item = &NormalRule> {
        self.0.iter()
    }

    pub fn into_iter(self) -> impl Iterator<Item = NormalRule> {
        self.0.into_iter()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Ground all variables in all possible ways.
    // TODO: less naïve grounding.
    pub fn ground(self) -> GroundProgram {
        let mut constants = Universe::new();
        self.constants(&mut constants);
        let constants = constants.into_iter().collect::<Vec<Constant>>();

        let mut variables = Names::new();
        self.variables(&mut variables);
        let variables = variables.into_iter().collect::<Vec<Symbol>>();

        let (mut rules, var_rules): (Vec<_>, Vec<_>) =
            self.into_iter().partition(|r| r.is_ground());

        // Knuth Algorithm 7.2.1.1L (Mixed-radix generation).
        let m = constants.len();
        let n = variables.len();
        let mut a = vec![0; n + 1];
        let bind = |a: &[usize]| -> Bindings {
            a.iter()
                .copied()
                .enumerate()
                .map(|(i, j)| (variables[i].clone(), constants[j].clone()))
                .collect::<Bindings>()
        };
        loop {
            let b = bind(&a[1..]);
            rules.extend(var_rules.iter().cloned().map(|r| r.ground(&b)));

            let mut j = n;
            while a[j] == m - 1 {
                a[j] = 0;
                j -= 1;
            }
            if j == 0 {
                break;
            }
            a[j] += 1;
        }

        GroundProgram::new(NormalProgram::new(rules))
    }
}

impl Formula for NormalProgram {
    fn atoms(&self, interp: &mut Interpretation) {
        for r in self.iter() {
            r.atoms(interp);
        }
    }

    fn constants(&self, universe: &mut Universe) {
        for r in self.iter() {
            r.constants(universe);
        }
    }

    fn variables(&self, names: &mut Names) {
        for r in self.iter() {
            r.variables(names);
        }
    }

    fn is_definite(&self) -> bool {
        self.iter().all(|r| r.is_definite())
    }

    fn is_ground(&self) -> bool {
        self.iter().all(|r| r.is_ground())
    }

    fn eval(&self, interp: &Interpretation) -> bool {
        self.iter().all(|r| r.eval(interp))
    }

    fn ground(self, bindings: &Bindings) -> Self {
        Self(self.into_iter().map(|r| r.ground(bindings)).collect())
    }

    fn reduce(self, interp: &Interpretation) -> Self {
        Self(self.into_iter().map(|r| r.reduce(interp)).collect())
    }
}

impl fmt::Display for NormalProgram {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for c in self.iter() {
            c.fmt(f)?;
            f.write_str("\n")?;
        }
        Ok(())
    }
}

/// Auxiliary atoms that represent rules.
pub type AuxAtoms = Vec<Atom>;

/// Fresh, unique atoms to associate with each rule.
// TODO: optionally use random numbers to avoid collisions.
pub fn genaux(aux: &str, id: usize, atoms: &Interpretation) -> Atom {
    assert!(!aux.is_empty(), "can't make an aux atom without a prefix");
    for i in 0..100 {
        let x = aux[aux.len() - 1..].repeat(i);
        let a = Atom::new(Symbol::new(format!("{aux}{x}_{id}")), vec![]);
        if !atoms.contains(&a) {
            return a;
        }
    }
    panic!("can't make an aux atom for this program");
}

/// A ground program contains no variables.
#[derive(Clone, Debug)]
pub struct GroundProgram(NormalProgram);

impl GroundProgram {
    fn new(program: NormalProgram) -> Self {
        assert!(program.iter().all(|r| r.is_ground()), "non-ground program");
        Self(program)
    }

    pub fn iter(&self) -> impl Iterator<Item = &NormalRule> {
        self.0.iter()
    }

    pub fn into_iter(self) -> impl Iterator<Item = NormalRule> {
        self.0.into_iter()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Program completion, also called Clark's completion. See Lifschitz, "ASP" §5.9.
    pub fn complete(self) -> CompleteProgram {
        // Index of which rules' heads contain a given atom.
        let mut heads = BTreeMap::<&Atom, BTreeSet<usize>>::new();
        for (i, rule) in self.iter().enumerate() {
            if let Some(a) = &rule.head {
                heads.entry(a).or_default().insert(i);
            }
        }

        // Build the constraints.
        let mut atoms = Interpretation::new();
        self.atoms(&mut atoms);
        let mut constraints = Vec::new();
        for rule in self.iter() {
            if let Some(head) = &rule.head {
                if atoms.remove(head) {
                    constraints.push(Constraint::new(
                        Some(head.clone()),
                        heads
                            .get(&head)
                            .map(|rules| {
                                rules
                                    .iter()
                                    .map(|&i| self.0 .0[i].body.clone())
                                    .collect::<Vec<_>>()
                            })
                            .unwrap_or_default(),
                    ));
                }
            } else {
                constraints.push(Constraint::new(None, vec![rule.body.clone()]));
            }
        }

        CompleteProgram::new(constraints)
    }
}

impl Formula for GroundProgram {
    fn atoms(&self, interp: &mut Interpretation) {
        self.0.atoms(interp)
    }

    fn constants(&self, universe: &mut Universe) {
        self.0.constants(universe)
    }

    fn variables(&self, names: &mut Names) {
        self.0.variables(names)
    }

    fn is_definite(&self) -> bool {
        self.iter().all(|r| r.is_definite())
    }

    fn is_ground(&self) -> bool {
        true
    }

    fn eval(&self, interp: &Interpretation) -> bool {
        self.0.eval(interp)
    }

    /// Assume we're already ground.
    fn ground(self, _bindings: &Bindings) -> Self {
        self
    }

    fn reduce(self, interp: &Interpretation) -> Self {
        Self(self.0.reduce(interp))
    }
}

impl fmt::Display for GroundProgram {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for c in self.iter() {
            c.fmt(f)?;
            f.write_str("\n")?;
        }
        Ok(())
    }
}

/// The result of completion is a set of constraints: equivalences
/// for each atom, where the body is now a *disjunction* of normal
/// (conjunctive) rule bodies; see Lifschitz, "ASP" §5.9.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Constraint {
    head: Option<Atom>,
    body: Vec<Vec<Literal>>,
}

impl Constraint {
    pub fn new(head: Option<Atom>, body: impl IntoIterator<Item = Vec<Literal>>) -> Self {
        Self {
            head,
            body: body.into_iter().collect(),
        }
    }
}

impl Formula for Constraint {
    fn atoms(&self, interp: &mut Interpretation) {
        for h in self.head.iter() {
            h.atoms(interp);
        }
        for b in self.body.iter() {
            for c in b {
                c.atoms(interp);
            }
        }
    }

    fn constants(&self, universe: &mut Universe) {
        for h in self.head.iter() {
            h.constants(universe);
        }
        for b in self.body.iter() {
            for c in b {
                c.constants(universe);
            }
        }
    }

    fn variables(&self, names: &mut Names) {
        for h in self.head.iter() {
            h.variables(names);
        }
        for b in self.body.iter() {
            for c in b {
                c.variables(names);
            }
        }
    }

    fn is_definite(&self) -> bool {
        self.head.iter().all(|h| h.is_definite())
            && self.body.iter().all(|b| b.iter().all(|c| c.is_definite()))
    }

    fn is_ground(&self) -> bool {
        self.head.iter().all(|h| h.is_ground())
            && self.body.iter().all(|b| b.iter().all(|c| c.is_ground()))
    }

    fn eval(&self, interp: &Interpretation) -> bool {
        self.head.as_ref().is_some_and(|head| interp.contains(head))
            == self.body.iter().any(|b| b.iter().all(|c| c.eval(interp)))
    }

    /// Assume we're already ground.
    fn ground(self, _bindings: &Bindings) -> Self {
        self
    }

    /// Delete each disjunct that has a negative literal `not b` with `b ∈ I`,
    /// and all negative literals in the conjuncts of the remaining disjuncts.
    fn reduce(self, interp: &Interpretation) -> Self {
        Self {
            head: self.head,
            body: self
                .body
                .into_iter()
                .filter_map(|b| {
                    if b.iter().any(|c| c.is_negative() && !c.eval(interp)) {
                        None
                    } else {
                        Some(b.into_iter().filter(|c| c.is_positive()).collect())
                    }
                })
                .collect(),
        }
    }
}

impl fmt::Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let body = self
            .body
            .iter()
            .map(|b| {
                format!(
                    "({})",
                    b.iter()
                        .map(|c| c.to_string())
                        .collect::<Vec<_>>()
                        .join(" and ")
                )
            })
            .collect::<Vec<_>>()
            .join(" or ");
        if let Some(head) = &self.head {
            f.write_fmt(format_args!("{} iff {}", head, body))
        } else {
            f.write_fmt(format_args!("iff {}", body))
        }
    }
}

#[derive(Clone, Debug)]
pub struct CompleteProgram(Vec<Constraint>);

impl CompleteProgram {
    fn new(program: impl IntoIterator<Item = Constraint>) -> Self {
        Self(program.into_iter().collect::<Vec<_>>())
    }

    pub fn iter(&self) -> impl Iterator<Item = &Constraint> {
        self.0.iter()
    }

    pub fn into_iter(self) -> impl Iterator<Item = Constraint> {
        self.0.into_iter()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl Formula for CompleteProgram {
    fn atoms(&self, interp: &mut Interpretation) {
        for r in self.iter() {
            r.atoms(interp);
        }
    }

    fn constants(&self, universe: &mut Universe) {
        for r in self.iter() {
            r.constants(universe);
        }
    }

    fn variables(&self, names: &mut Names) {
        for r in self.iter() {
            r.variables(names);
        }
    }

    fn is_definite(&self) -> bool {
        self.iter().all(|c| c.is_definite())
    }

    fn is_ground(&self) -> bool {
        self.iter().all(|c| c.is_ground())
    }

    fn eval(&self, interp: &Interpretation) -> bool {
        self.iter().all(|c| c.eval(interp))
    }

    fn ground(self, bindings: &Bindings) -> Self {
        Self(self.into_iter().map(|r| r.ground(bindings)).collect())
    }

    fn reduce(self, interp: &Interpretation) -> Self {
        Self(self.into_iter().map(|r| r.reduce(interp)).collect())
    }
}

impl fmt::Display for CompleteProgram {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for c in self.iter() {
            c.fmt(f)?;
            f.write_str("\n")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! nrule {
        [$($rule:tt)*] => {{
            let mut n = NormalRule::normalize(&rule![$($rule)*]);
            assert_eq!(n.len(), 1);
            n.remove(0)
        }}
    }

    macro_rules! constraint {
        [iff $(($($body:tt)*))or+] => {{
            Constraint::new(
                None,
                vec![$(rule![if $($body)*].body),+]
            )
        }};
        [$head:ident$(($($arg:tt),*))? iff $(($($body:tt)*))or*] => {{
            Constraint::new(
                Some(atom![$head$(($($arg),*))?]),
                vec![$(rule![if $($body)*].body),*]
            )
        }}
    }

    macro_rules! interp {
        {$($head:ident$(($($arg:tt),*))?),*} => {
            [$(atom![$head$(($($arg),*))?]),*]
                .into_iter()
                .collect::<Interpretation>()
        }
    }

    /// Grounding requires us to collect all the unique constants in a rule,
    /// i.e., its Herbrand Universe.
    #[test]
    fn rule_constants() {
        let mut constants = Universe::new();
        rule![p(a, b) if q(b) and f(X) and r(s, t)].constants(&mut constants);
        assert_eq!(
            constants.into_iter().collect::<Vec<_>>(),
            vec![sym![a], sym![b], sym![s], sym![t]]
        );
    }

    /// "Rule shifting" turns a disjunctive rule into a set of normal rules
    /// (with at most one head atom).
    #[test]
    fn normalize_disjunctive_rule() {
        let r = rule![(a or b or c) if d and e];
        let n = NormalRule::normalize(&r);
        assert_eq!(n.len(), 3);
        assert_eq!(n[0], nrule![a if d and e and not b and not c]);
        assert_eq!(n[1], nrule![b if d and e and not a and not c]);
        assert_eq!(n[2], nrule![c if d and e and not a and not b]);
    }

    #[test]
    fn normalize_constraint() {
        let r = rule![if p and q];
        let n = NormalRule::normalize(&r);
        assert_eq!(n.len(), 1);
        assert_eq!(n[0], nrule![if p and q]);
    }

    /// This program is already ground.
    #[test]
    fn ground_trivial_0() {
        let program = Program::new([rule![a or b or c]]).normalize();
        assert_eq!(
            program.iter().cloned().collect::<Vec<_>>(),
            vec![
                nrule![a if not b and not c],
                nrule![b if not a and not c],
                nrule![c if not a and not b]
            ]
        );

        let ground = program.clone().ground();
        assert_eq!(
            ground.into_iter().collect::<Vec<_>>(),
            program.into_iter().collect::<Vec<_>>()
        );
    }

    /// This program needs a bit of grounding.
    #[test]
    fn ground_trivial_1() {
        let rules = [rule![p(X) if p(a) and p(b)]];
        let program = Program::new(rules).normalize();
        assert_eq!(
            program.iter().cloned().collect::<Vec<_>>(),
            [nrule![p(X) if p(a) and p(b)]]
        );

        let ground = program.ground();
        assert_eq!(
            ground.into_iter().collect::<Vec<_>>(),
            vec![nrule![p(a) if p(a) and p(b)], nrule![p(b) if p(a) and p(b)]],
        );
    }

    /// And this one needs a bit more.
    #[test]
    fn ground_gelfond_lifschitz_5() {
        let rules = [rule![p(a, b)], rule![q(X) if p(X, Y) and not q(Y)]];
        let ground = Program::new(rules).normalize().ground();
        assert_eq!(
            ground.into_iter().collect::<Vec<_>>(),
            vec![
                nrule![p(a, b)],
                nrule![q(a) if p(a, a) and not q(a)],
                nrule![q(a) if p(a, b) and not q(b)],
                nrule![q(b) if p(b, a) and not q(a)],
                nrule![q(b) if p(b, b) and not q(b)],
            ]
        );
    }

    #[test]
    fn complete_trivial_0() {
        let rules = [rule![p]];
        let program = Program::new(rules).normalize().ground().complete();
        assert_eq!(
            program.into_iter().collect::<Vec<_>>(),
            [constraint![p iff ()]]
        );
    }

    #[test]
    fn complete_trivial_1() {
        let rules = [rule![a if b]];
        let program = Program::new(rules).normalize().ground().complete();
        assert_eq!(
            program.into_iter().collect::<Vec<_>>(),
            [constraint![a iff (b)]]
        );
    }

    #[test]
    fn complete_constraint() {
        let rules = [rule![if p and q]];
        let program = Program::new(rules).normalize().ground().complete();
        assert_eq!(
            program.into_iter().collect::<Vec<_>>(),
            [constraint![iff (p and q)]]
        );
    }

    /// Dodaro example 10.
    #[test]
    fn complete_dodaro_example_10() {
        let rules = [rule![(a or b)], rule![(c or d) if a]];
        let program = Program::new(rules).normalize().ground();
        assert_eq!(
            program.iter().cloned().collect::<Vec<_>>(),
            [
                nrule![a if not b],
                nrule![b if not a],
                nrule![c if a and not d],
                nrule![d if a and not c]
            ]
        );

        let complete = program.complete();
        assert_eq!(
            complete.into_iter().collect::<Vec<_>>(),
            [
                constraint![a iff (not b)],
                constraint![b iff (not a)],
                constraint![c iff (a and not d)],
                constraint![d iff (a and not c)],
            ]
        );
    }

    /// Alviano and Dodaro, "Completion of Disjunctive Logic Programs" (IJCAI-16).
    #[test]
    fn complete_alviano_dodaro_example_1() {
        let rules = [rule![a or b or c], rule![b if a], rule![c if not a]];
        let program = Program::new(rules).normalize().ground();
        assert_eq!(
            program.iter().cloned().collect::<Vec<_>>(),
            [
                nrule![a if not b and not c],
                nrule![b if not a and not c],
                nrule![c if not a and not b],
                nrule![b if a],
                nrule![c if not a]
            ]
        );

        let complete = program.complete();
        assert_eq!(
            complete.into_iter().collect::<Vec<_>>(),
            [
                constraint![a iff (not b and not c)],
                constraint![b iff (not a and not c) or (a)],
                constraint![c iff (not a and not b) or (not a)],
            ]
        );
    }

    /// Lifschitz, "ASP", §5.2.
    #[test]
    fn reduce_asp_5_2() {
        // Rules (5.1)-(5.4).
        let rules = [rule![p], rule![q], rule![r if p and not s], rule![s if q]];
        let program = Program::new(rules).normalize().ground().complete();
        assert_eq!(
            program.iter().cloned().collect::<Vec<_>>(),
            [
                constraint![p iff ()],
                constraint![q iff ()],
                constraint![r iff (p and not s)],
                constraint![s iff (q)],
            ]
        );

        // Reduct (5.10).
        let interp = interp! {p, q, s};
        let reduct = program.clone().reduce(&interp);
        assert_eq!(
            reduct.into_iter().collect::<Vec<_>>(),
            [
                constraint![p iff ()],
                constraint![q iff ()],
                constraint![r iff],
                constraint![s iff (q)],
            ]
        );
        assert!(program.eval(&interp));

        // Reduct (5.11).
        let interp = interp! {p, q};
        let reduct = program.clone().reduce(&interp);
        assert_eq!(
            reduct.iter().cloned().collect::<Vec<_>>(),
            [
                constraint![p iff ()],
                constraint![q iff ()],
                constraint![r iff (p)],
                constraint![s iff (q)],
            ]
        );
        assert!(!reduct.eval(&interp));
    }

    #[test]
    fn reduce_alviano_dodaro_example_1() {
        let rules = [rule![a or b or c], rule![b if a], rule![c if not a]];
        let program = Program::new(rules).normalize().ground().complete();
        let interp = interp! {c};
        let reduct = program.clone().reduce(&interp);
        assert_eq!(
            reduct.into_iter().collect::<Vec<_>>(),
            [
                constraint![a iff],
                constraint![b iff (a)],
                constraint![c iff () or ()],
            ]
        );
        assert!(program.eval(&interp));
    }
}
