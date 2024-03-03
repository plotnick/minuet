//! Meaning-preserving manipulation of logic programs: ground all variables,
//! normalize propositional images, and complete rules by transforming them
//! from implications into equivalences.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::ops::Index;

use crate::clause::{Clause, Conjunction, Disjunction, Dnf};
use crate::formula::{Bindings, Formula, Groundable, Interpretation, Names, Universe};
use crate::generate::combinations_mixed;
use crate::image::{Context, PropositionalImage as _};
use crate::syntax::*;
use crate::tracer::Trace;

/// A program is a collection of rules, which we'll preprocess prior to
/// compilation in a strict sequence of meaning-preserving steps. Each
/// step generates a new (potentially exponentially larger) program of a
/// different type. There is a unique method of one argument (trace level)
/// on each program type that advances to the next step; e.g., `ground`,
/// `image`, `normalize`, `shift`, `complete`.
#[derive(Clone, Debug)]
pub struct Program<R>(Vec<R>);

impl<R> Program<R> {
    pub fn new(rules: impl IntoIterator<Item = R>) -> Self {
        Self(rules.into_iter().collect())
    }

    pub fn iter(&self) -> impl Iterator<Item = &R> {
        self.0.iter()
    }

    pub fn into_iter(self) -> impl Iterator<Item = R> {
        self.0.into_iter()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<R> Formula for Program<R>
where
    R: Formula,
{
    fn atoms(&self, interp: &mut Interpretation) {
        for rule in self.iter() {
            rule.atoms(interp);
        }
    }

    fn eval(&self, interp: &Interpretation) -> bool {
        self.iter().all(|rule| rule.eval(interp))
    }

    fn is_positive(&self) -> bool {
        self.iter().all(|rule| rule.is_positive())
    }
}

impl<R> Index<usize> for Program<R> {
    type Output = R;

    fn index(&self, index: usize) -> &Self::Output {
        self.0.index(index)
    }
}

impl<R> fmt::Display for Program<R>
where
    R: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for c in self.iter() {
            c.fmt(f)?;
            f.write_str("\n")?;
        }
        Ok(())
    }
}

impl Program<BaseRule<Term>> {
    /// A convenience method to "skip to the end": run through each
    /// preprocessing step in sequence and return the result.
    pub fn preprocess(self, trace: Trace) -> Program<CompleteRule> {
        self.ground_with_trace(trace)
            .image(trace)
            .normalize(trace)
            .shift(trace)
            .complete(trace)
    }

    pub fn ground_with_trace(self, trace: Trace) -> Program<BaseRule<GroundTerm>> {
        trace!(trace, Preprocess, "Base program:\n{self}");
        let grounded = self.ground();
        trace!(trace, Preprocess, "Grounded program:\n{grounded}");
        grounded
    }
}

impl Groundable for Program<BaseRule<Term>> {
    type Ground = Program<BaseRule<GroundTerm>>;

    fn is_ground(&self) -> bool {
        self.iter().all(|rule| rule.is_ground())
    }

    /// The first step in program preprocessing is grounding: find all
    /// constants, and bind all variables to them in all possible ways.
    /// The zero-argument step method is `ground`, which punts to this.
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

    /// Ground one rule.
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

impl Program<BaseRule<GroundTerm>> {
    /// The next step in program preprocessing is finding the propositional
    /// image of each rule.
    pub fn image(self, trace: Trace) -> Program<PropositionalRule> {
        let image = Program::new(self.into_iter().flat_map(BaseRule::<GroundTerm>::image));
        trace!(trace, Preprocess, "Propositional image:\n{image}");
        image
    }
}

/// A propositional rule has arbitrary (ground) clauses as head and body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PropositionalRule {
    pub head: Clause,
    pub body: Clause,
}

impl fmt::Display for PropositionalRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("{} ← {}", self.head, self.body))
    }
}

impl BaseRule<GroundTerm> {
    /// Find the propositional image of one base rule (which may be more
    /// than one propositional rule). See the `PropositionalImage` trait
    /// for details.
    fn image(self) -> Vec<PropositionalRule> {
        match self {
            Self::Choice(ChoiceRule { head, body }) => head
                .image(Context::Head)
                .into_iter()
                .map(|head| PropositionalRule {
                    head,
                    body: Clause::and(body.iter().cloned().map(Clause::Lit)),
                })
                .collect(),
            Self::Disjunctive(Rule { head, body }) => vec![PropositionalRule {
                head: Clause::or(head.into_iter().map(|h| h.image(Context::Head))),
                body: Clause::and(body.into_iter().map(|b| b.image(Context::Body))),
            }],
        }
    }
}

impl Program<PropositionalRule> {
    /// The next preprocessing step is normalization, where we bring the head
    /// and body into a canonical form. See "ASP" and Lifschitz & Tang (1999),
    /// "Nested Expressions in Logic Programs".
    pub fn normalize(self, trace: Trace) -> Program<NormalRule> {
        let normalized = Program::new(self.into_iter().flat_map(PropositionalRule::normalize));
        trace!(trace, Preprocess, "Normalized program:\n{normalized}");
        normalized
    }
}

impl PropositionalRule {
    /// Normalize one rule. We use an intermediate semi-normal form,
    /// and expand all nontrivial con/disjunctions in the head/body.
    fn normalize(self) -> Vec<NormalRule> {
        // Bring the head/body into dis/conjunctive normal form.
        let head = self.head.dnf();
        let body = self.body.cnf();

        // Replace nontrivial disjunctions in the body as described
        // in "ASP" exercise 4.7 (c): p ← q ∨ r = {p ← q, p ← r},
        #[derive(Debug)]
        struct BodyNormalizedRule {
            head: Dnf,
            body: Conjunction<Literal<GroundTerm>>,
        }
        impl BodyNormalizedRule {
            fn new(head: Dnf, body: Conjunction<Literal<GroundTerm>>) -> Self {
                Self { head, body }
            }
        }

        let rules = if body.iter().any(|x| x.len() > 1) {
            // Break nontrivial disjunctions into multiple rules.
            body.dnf()
                .into_iter()
                .map(|body| BodyNormalizedRule::new(head.clone(), body))
                .collect()
        } else {
            // Normalize and hoist trivial disjunctions.
            vec![BodyNormalizedRule::new(
                head,
                Conjunction::from_iter(body.into_iter().map(|d| match d.len() {
                    0 => Self::f(),
                    1 => d.into_iter().next().expect("missing disjunct"),
                    _ => unreachable!("nontrivial disjunction"),
                })),
            )]
        };

        // Replace nontrivial conjunctions in the head as described
        // in "ASP" §5.4: p ∧ q ∧ r ← s = {p ← s, q ← s, r ← s}.
        rules
            .into_iter()
            .flat_map(|BodyNormalizedRule { head, body }| {
                if head.iter().any(|x| x.len() > 1) {
                    // Break nontrivial conjunctions into multiple rules.
                    head.cnf()
                        .into_iter()
                        .map(|head| NormalRule::new(head, body.clone()))
                        .collect()
                } else {
                    // Normalize and hoist trivial conjunctions.
                    vec![NormalRule::new(
                        Disjunction::from_iter(head.into_iter().map(|c| match c.len() {
                            0 => Self::t(),
                            1 => c.into_iter().next().expect("missing conjunct"),
                            _ => unreachable!("nontrivial conjunction"),
                        })),
                        body,
                    )]
                }
            })
            .collect()
    }

    /// A normal representation of _true_: `0 = 0`.
    fn t() -> Literal<GroundTerm> {
        let zero = GroundTerm::Constant(Constant::Number(0));
        Literal::relation(zero.clone(), RelOp::Eq, zero)
    }

    /// A normal representation of _false_: `0 != 0`.
    fn f() -> Literal<GroundTerm> {
        Self::t().negate()
    }
}

/// A strictly disjunctive head and strictly conjunctive body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NormalRule {
    head: Disjunction<Literal<GroundTerm>>,
    body: Conjunction<Literal<GroundTerm>>,
}

impl NormalRule {
    fn new(head: Disjunction<Literal<GroundTerm>>, body: Conjunction<Literal<GroundTerm>>) -> Self {
        Self { head, body }
    }
}

impl fmt::Display for NormalRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("{} ← {}", self.head, self.body))
    }
}

impl Program<NormalRule> {
    /// The penultimate program preprocessing step is shifting, wherein we
    /// produce a set of rules with at most one positive atom for a head;
    /// see Lifschitz, "ASP" §5.8 and Dodaro definition 10.
    pub fn shift(self, trace: Trace) -> Program<ShiftedRule> {
        let shifted = Program::new(self.into_iter().flat_map(NormalRule::shift));
        trace!(trace, Preprocess, "Shifted program:\n{shifted}");
        shifted
    }
}

impl NormalRule {
    /// Shift one rule: keep positive atoms in the head, move negative ones
    /// to the body.
    fn shift(self) -> Vec<ShiftedRule> {
        let (positive, negative): (Vec<_>, Vec<_>) =
            self.head.into_iter().partition(|l| l.is_positive());
        let head: Interpretation =
            positive
                .into_iter()
                .fold(Interpretation::new(), |mut atoms, clause| {
                    clause.atoms(&mut atoms);
                    atoms
                });

        let body = self.body.and_also(negative.into_iter().map(|c| c.negate()));
        if head.is_empty() {
            vec![ShiftedRule::new(None, body)]
        } else {
            head.iter()
                .map(|h| {
                    ShiftedRule::new(
                        Some(h.clone()),
                        body.clone().and_also(head.iter().filter_map(|a| {
                            if a != h {
                                Some(Literal::Negative(a.clone()))
                            } else {
                                None
                            }
                        })),
                    )
                })
                .collect()
        }
    }
}

/// A shifted rule has at most one (positive) head atom and
/// a (possibly empty) conjunctive body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ShiftedRule {
    head: Option<Atom<GroundTerm>>,
    body: Conjunction<Literal<GroundTerm>>,
}

impl ShiftedRule {
    fn new(head: Option<Atom<GroundTerm>>, body: Conjunction<Literal<GroundTerm>>) -> Self {
        Self { head, body }
    }
}

impl Formula for ShiftedRule {
    fn atoms(&self, interp: &mut Interpretation) {
        if let Some(h) = self.head.as_ref() {
            h.atoms(interp);
        }
        self.body.iter().for_each(|b| b.atoms(interp));
    }

    fn is_positive(&self) -> bool {
        self.head.iter().all(|h| h.is_positive()) && self.body.iter().all(|b| b.is_positive())
    }

    fn eval(&self, interp: &Interpretation) -> bool {
        self.head.iter().any(|h| h.eval(interp)) && self.body.iter().all(|b| b.eval(interp))
    }
}

impl fmt::Display for ShiftedRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!(
            "{} ← {}",
            self.head
                .as_ref()
                .map(|h| h.to_string())
                .unwrap_or_else(|| String::from("⊥")),
            self.body
        ))
    }
}

impl Program<ShiftedRule> {
    /// The last preprocessing step prior to compilation and solving is
    /// called _Clark's completion_. It turns each implication into an
    /// equivalence; see Lifschitz, "ASP" §5.9 and Dodaro §3.3.
    pub fn complete(self, trace: Trace) -> Program<CompleteRule> {
        // Which rules' heads contain a given atom.
        let mut heads = BTreeMap::<Atom<GroundTerm>, BTreeSet<usize>>::new();
        for (i, rule) in self.iter().enumerate() {
            if let Some(a) = &rule.head {
                heads.entry(a.clone()).or_default().insert(i);
            }
        }

        let mut atoms = Interpretation::new();
        self.atoms(&mut atoms);
        let mut rules = Vec::new();
        for rule in self.iter() {
            match &rule.head {
                None => rules.push(CompleteRule::new(
                    None,
                    Disjunction::from_iter([rule.body.clone()]),
                )),
                Some(head) => {
                    if atoms.remove(head) {
                        let bodies = heads
                            .get(head)
                            .map(|rules| {
                                Disjunction::from_iter(rules.iter().map(|&i| self[i].body.clone()))
                            })
                            .unwrap_or_default();
                        rules.push(CompleteRule::new(Some(head.clone()), bodies));
                    }
                }
            }
        }
        // TODO: if !atoms.is_empty() { trace: atoms unused in any head }

        let completed = Program::new(rules);
        trace!(trace, Preprocess, "Completed program:\n{completed}");
        completed
    }
}

/// The result of completion is a set of equivalences for each head atom,
/// where the body is now a *disjunction* of normal (conjunctive, grounded)
/// rule bodies; see Lifschitz, "ASP" §5.9.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompleteRule {
    head: Option<Atom<GroundTerm>>,
    body: Dnf,
}

impl CompleteRule {
    pub fn new(head: Option<Atom<GroundTerm>>, body: Dnf) -> Self {
        Self { head, body }
    }
}

impl Formula for CompleteRule {
    fn atoms(&self, interp: &mut Interpretation) {
        if let Some(h) = self.head.as_ref() {
            h.atoms(interp);
        }
        self.body.atoms(interp);
    }

    fn is_positive(&self) -> bool {
        self.head.iter().all(|h| h.is_positive()) && self.body.is_positive()
    }

    fn eval(&self, interp: &Interpretation) -> bool {
        self.head.as_ref().is_some_and(|h| h.eval(interp)) == self.body.eval(interp)
    }
}

impl fmt::Display for CompleteRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!(
            "{} ↔ {}",
            self.head
                .as_ref()
                .map(|h| h.to_string())
                .unwrap_or_else(|| String::from("⊥")),
            self.body
        ))
    }
}

impl Program<CompleteRule> {
    /// The very last step in program processing is checking for model
    /// stability, which requires _reducing_ the program by a potential
    /// solution and checking that its solution agrees with that of the
    /// unreduced program. We do not currently define a different type
    /// for the reduced program; the only difference is that it's always
    /// positive (definite, i.e., negation-free).
    pub fn reduce(self, interp: &Interpretation) -> Self {
        Self(self.into_iter().map(|r| r.reduce(interp)).collect())
    }
}

impl CompleteRule {
    /// Reduce one rule: delete each disjunct that has a negative literal `not b`
    /// with `b ∈ I`, and all negative literals in the conjuncts of the remaining
    /// disjuncts.
    fn reduce(self, interp: &Interpretation) -> Self {
        Self {
            head: self.head,
            body: Disjunction::from_iter(self.body.into_iter().filter_map(|b| {
                if !b.is_positive() && !b.eval(interp) {
                    None
                } else {
                    Some(Conjunction::from_iter(
                        b.into_iter().filter(|c| c.is_positive()),
                    ))
                }
            })),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! nrule {
        [if $(($($body:tt)*))and+] => {
            NormalRule::new(
                Disjunction::f(),
                Conjunction::from_iter([$(glit![$($body)*]),+])
            )
        };
        [$head:ident($($args:tt)*) if $(($($body:tt)*))and*] => {
            NormalRule::new(
                Disjunction::from_iter(gatom![$head($($args)*)]),
                Conjunction::from_iter([$(glit![$body]),*])
            )
        };
        [$(($($head:tt)*))or*] => {
            NormalRule::new(
                Disjunction::from_iter([$(glit![$($head)*]),*]),
                Conjunction::from_iter([])
            )
        };
        [$(($($head:tt)*))or* if $(($($body:tt)*))and*] => {
            NormalRule::new(
                Disjunction::from_iter([$(glit![$($head)*]),*]),
                Conjunction::from_iter([$(glit![$($body)*]),*])
            )
        };
    }

    macro_rules! srule {
        [if $(($($body:tt)*))and+] => {
            ShiftedRule::new(
                None,
                Conjunction::from_iter([$(glit![$($body)*]),+])
            )
        };
        [$head:ident($($args:tt)*) if $(($($body:tt)*))and*] => {
            ShiftedRule::new(
                Some(gatom![$head($($args)*)]),
                Conjunction::from_iter([$(glit![$($body)*]),*])
            )
        };
        [$head:ident if $(($($body:tt)*))and*] => {
            ShiftedRule::new(
                Some(gatom![$head]),
                Conjunction::from_iter([$(glit![$($body)*]),*])
            )
        };
    }

    macro_rules! crule {
        [iff $(($(($($conj:tt)*))and*))or*] => {
            CompleteRule::new(
                None,
                Disjunction::from_iter([$(Conjunction::from_iter([$(glit![$($conj)*]),*])),*])
            )
        };
        [$head:ident($($args:tt)*) iff $(($(($($conj:tt)*))and*))or*] => {
            CompleteRule::new(
                Some(gatom![$head($($args)*)]),
                Disjunction::from_iter([$(Conjunction::from_iter([$(glit![$($conj)*]),*])),*])
            )
        };
        [$head:ident iff $(($(($($conj:tt)*))and*))or*] => {
            CompleteRule::new(
                Some(gatom![$head]),
                Disjunction::from_iter([$(Conjunction::from_iter([$(glit![$($conj)*]),*])),*])
            )
        };
    }

    macro_rules! interp {
        {$($head:ident$(($($arg:tt),*))?),*} => {
            [$(gatom![$head$(($($arg),*))?]),*]
                .into_iter()
                .collect::<Interpretation>()
        }
    }

    /// This program is already ground.
    #[test]
    fn ground_trivial_0() {
        let ground = Program::new([rule![a or b or c]]).ground();
        assert_eq!(
            ground.iter().cloned().collect::<Vec<_>>(),
            vec![rule![a or b or c].ground()]
        );
    }

    /// This program needs a bit of grounding.
    #[test]
    fn ground_trivial_1() {
        let rules = [rule![p(X) if p(a) and p(b)]];
        let ground = Program::new(rules).ground();
        assert_eq!(
            ground.iter().cloned().collect::<Vec<_>>(),
            [
                rule![p(a) if p(a) and p(b)].ground(),
                rule![p(b) if p(a) and p(b)].ground()
            ]
        );
    }

    /// And this one needs a bit more.
    #[test]
    fn ground_gelfond_lifschitz_5() {
        let rules = [rule![p(1, 2)], rule![q(X) if p(X, Y) and not q(Y)]];
        let ground = Program::new(rules).ground();
        assert_eq!(
            ground.into_iter().collect::<Vec<_>>(),
            vec![
                rule![p(1, 2)].ground(),
                rule![q(1) if p(1, 1) and not q(1)].ground(),
                rule![q(1) if p(1, 2) and not q(2)].ground(),
                rule![q(2) if p(2, 1) and not q(1)].ground(),
                rule![q(2) if p(2, 2) and not q(2)].ground(),
            ]
        );
    }

    #[test]
    fn normalize_constraint() {
        let mut images = rule![if p and q].ground().image();
        assert_eq!(images.len(), 1);
        assert_eq!(images.remove(0).normalize(), [nrule![if (p) and (q)]]);
    }

    #[test]
    fn normalize_choice() {
        let mut images = rule![{ p }].ground().image();
        assert_eq!(images.len(), 1);
        assert_eq!(images.remove(0).normalize(), [nrule![(p) or (not p)]]);
    }

    #[test]
    fn normalize_choices() {
        let mut images = rule![{p or q or r}].ground().image();
        assert_eq!(images.len(), 3);
        assert_eq!(images.remove(2).normalize(), [nrule![(r) or (not r)]]);
        assert_eq!(images.remove(1).normalize(), [nrule![(q) or (not q)]]);
        assert_eq!(images.remove(0).normalize(), [nrule![(p) or (not p)]]);
    }

    #[test]
    fn shift_disjunctive_rule() {
        let n = nrule![(a) or (b) or (c) if (d) and (e)];
        assert_eq!(
            n.shift(),
            [
                srule![a if (d) and (e) and (not b) and (not c)],
                srule![b if (d) and (e) and (not a) and (not c)],
                srule![c if (d) and (e) and (not a) and (not b)]
            ]
        );
    }

    #[test]
    fn shift_head_negation() {
        assert_eq!(nrule![(not q)].shift(), vec![srule![if (not not q)]]);
        assert_eq!(
            nrule![(p) or (not q)].shift(),
            vec![srule![p if (not not q)]]
        );
    }

    #[test]
    fn shift_double_head_negation() {
        assert_eq!(nrule![(not not q)].shift(), vec![srule![if (not q)]]);
        assert_eq!(
            nrule![(p) or (not not q)].shift(),
            vec![srule![p if (not q)]]
        );
    }

    #[test]
    fn complete_trivial_0() {
        let rules = [rule![p]];
        let complete = Program::new(rules).preprocess(Trace::none());
        assert_eq!(complete.into_iter().collect::<Vec<_>>(), [crule![p iff ()]]);
    }

    #[test]
    fn complete_trivial_1() {
        let rules = [rule![a if b]];
        let complete = Program::new(rules).preprocess(Trace::none());
        assert_eq!(
            complete.into_iter().collect::<Vec<_>>(),
            [crule![a iff ((b))]]
        );
    }

    #[test]
    fn complete_constraint() {
        let rules = [rule![if p and q]];
        let complete = Program::new(rules).preprocess(Trace::none());
        assert_eq!(
            complete.into_iter().collect::<Vec<_>>(),
            [crule![iff ((p) and (q))]]
        );
    }

    /// Dodaro, example 10.
    #[test]
    fn complete_dodaro_example_10() {
        let rules = [rule![a or b], rule![c or d if a]];
        let complete = Program::new(rules).preprocess(Trace::none());
        assert_eq!(
            complete.into_iter().collect::<Vec<_>>(),
            [
                crule![a iff ((not b))],
                crule![b iff ((not a))],
                crule![c iff ((a) and (not d))],
                crule![d iff ((a) and (not c))],
            ]
        );
    }

    /// Alviano and Dodaro, "Completion of Disjunctive Logic Programs" (IJCAI-16).
    #[test]
    fn complete_alviano_dodaro_example_1() {
        let rules = [rule![a or b or c], rule![b if a], rule![c if not a]];
        let complete = Program::new(rules).preprocess(Trace::none());
        assert_eq!(
            complete.into_iter().collect::<Vec<_>>(),
            [
                crule![a iff ((not b) and (not c))],
                crule![b iff ((not a) and (not c)) or ((a))],
                crule![c iff ((not a) and (not b)) or ((not a))],
            ]
        );
    }

    /// Lifschitz, "ASP", §5.2.
    #[test]
    fn reduce_asp_5_2() {
        // Rules (5.1)-(5.4).
        let rules = [rule![p], rule![q], rule![r if p and not s], rule![s if q]];
        let complete = Program::new(rules).preprocess(Trace::none());
        assert_eq!(
            complete.iter().cloned().collect::<Vec<_>>(),
            [
                crule![p iff ()],
                crule![q iff ()],
                crule![r iff ((p) and (not s))],
                crule![s iff ((q))],
            ]
        );

        // Reduct (5.10).
        let interp = interp! {p, q, s};
        let reduct = complete.clone().reduce(&interp);
        assert_eq!(
            reduct.into_iter().collect::<Vec<_>>(),
            [
                crule![p iff ()],
                crule![q iff ()],
                crule![r iff],
                crule![s iff ((q))],
            ]
        );
        assert!(complete.eval(&interp));

        // Reduct (5.11).
        let interp = interp! {p, q};
        let reduct = complete.clone().reduce(&interp);
        assert_eq!(
            reduct.iter().cloned().collect::<Vec<_>>(),
            [
                crule![p iff ()],
                crule![q iff ()],
                crule![r iff ((p))],
                crule![s iff ((q))],
            ]
        );
        assert!(!reduct.eval(&interp));
    }

    #[test]
    fn reduce_alviano_dodaro_example_1() {
        let rules = [rule![a or b or c], rule![b if a], rule![c if not a]];
        let program = Program::new(rules).preprocess(Trace::none());
        let interp = interp! {c};
        let reduct = program.clone().reduce(&interp);
        assert_eq!(
            reduct.into_iter().collect::<Vec<_>>(),
            [crule![a iff], crule![b iff ((a))], crule![c iff () or ()],]
        );
        assert!(program.eval(&interp));
    }

    #[test]
    fn complete_excluded_middle() {
        let rules = [rule![p or not p]];
        let complete = Program::new(rules).preprocess(Trace::none());
        assert_eq!(
            complete.into_iter().collect::<Vec<_>>(),
            [crule![p iff ((not not p))]]
        );
    }

    /// Lifschitz, "ASP" §5.4.
    #[test]
    fn reduce_excluded_middle() {
        let rules = [rule![p or not p]];
        let complete = Program::new(rules).preprocess(Trace::none());

        let interp = interp! {};
        let reduct = complete.clone().reduce(&interp);
        assert!(reduct.eval(&interp));
        assert_eq!(reduct.into_iter().collect::<Vec<_>>(), [crule![p iff]]);

        let interp = interp! {p};
        let reduct = complete.clone().reduce(&interp);
        assert!(reduct.eval(&interp));
        assert_eq!(reduct.into_iter().collect::<Vec<_>>(), [crule![p iff ()]]);
    }
}
