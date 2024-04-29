//! A program is a collection of rules, which we'll preprocess prior to
//! compilation in a strict sequence of meaning-preserving steps. Each
//! step generates a new (potentially exponentially larger) program of a
//! different type. There is a unique method of one argument (trace level)
//! on each program type that advances to the next step; e.g., `ground`,
//! `image`, `normalize`, `shift`, `complete`.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::ops::Index;

use minuet_syntax::*;
use minuet_tracer::*;

use crate::clause::{Clause, Conjunction, Disjunction, Dnf};
use crate::formula::{Atoms, Formula, Interpretation};
use crate::ground::{GroundTerm, Groundable as _};
use crate::image::{Bounds as _, Context, PropositionalImage as _};

/// A collection of rules.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Program<R>(Vec<R>);

impl<R> Program<R> {
    pub fn new(rules: impl IntoIterator<Item = R>) -> Self {
        Self(rules.into_iter().collect())
    }

    pub fn as_slice(&self) -> &[R] {
        self.0.as_slice()
    }

    pub fn iter(&self) -> impl Iterator<Item = &R> {
        self.0.iter()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<R> Atoms for Program<R>
where
    R: Atoms,
{
    fn atoms(&self, interp: &mut Interpretation) {
        for rule in self.iter() {
            rule.atoms(interp);
        }
    }
}

impl<R> Formula for Program<R>
where
    R: Formula,
{
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

impl<R> IntoIterator for Program<R> {
    type Item = R;
    type IntoIter = <Vec<R> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
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
        trace!(trace, Preprocess, "Base program:\n{self}");
        self.ground_program(trace)
            .image(trace)
            .normalize(trace)
            .shift(trace)
            .complete(trace)
    }

    /// The first step in program preprocessing is grounding: replace
    /// all terms over variables with ground (variable-free) terms.
    /// See the `Groundable` trait for details.
    pub fn ground_program(self, trace: Trace) -> Program<BaseRule<GroundTerm>> {
        let grounded = self.ground();
        trace!(trace, Preprocess, "Grounded program:\n{grounded}");
        grounded
    }
}

impl Program<BaseRule<GroundTerm>> {
    /// The next step in program preprocessing is finding the propositional
    /// image (logical formula representation) of each rule.
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

trait RuleImage {
    type Image;

    fn image(self) -> Vec<Self::Image>;
}

impl RuleImage for BaseRule<GroundTerm> {
    type Image = PropositionalRule;

    /// Find the propositional image of one base rule (which may be more
    /// than one propositional rule). See the `PropositionalImage` trait
    /// for details.
    fn image(self) -> Vec<Self::Image> {
        match self {
            Self::Choice(ChoiceRule { head, body }) => {
                let bounds = head.clone().bounds();
                let head_image = head.image(Context::Head);
                let body_image = Clause::and(body.into_iter().map(|b| b.image(Context::Body)));
                head_image
                    .into_iter()
                    .map(|head| PropositionalRule {
                        head,
                        body: body_image.clone(),
                    })
                    .chain(bounds.into_iter().map(|bound| PropositionalRule {
                        head: Clause::f(),
                        body: Clause::and(bound.and_also(body_image.clone())),
                    }))
                    .collect()
            }
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

impl Atoms for ShiftedRule {
    fn atoms(&self, interp: &mut Interpretation) {
        if let Some(h) = self.head.as_ref() {
            h.atoms(interp);
        }
        self.body.iter().for_each(|b| b.atoms(interp));
    }
}

impl Formula for ShiftedRule {
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

impl Atoms for CompleteRule {
    fn atoms(&self, interp: &mut Interpretation) {
        if let Some(h) = self.head.as_ref() {
            h.atoms(interp);
        }
        self.body.atoms(interp);
    }
}

impl Formula for CompleteRule {
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
        ([$($head: expr),*], [$($body: expr),*]) => {
            NormalRule::new(
                Disjunction::from_iter([$($head),*]),
                Conjunction::from_iter([$($body),*])
            )
        };
    }

    macro_rules! srule {
        ([], [$($body: expr),*]) => {
            ShiftedRule::new(
                None,
                Conjunction::from_iter([$($body),*])
            )
        };
        ($head: tt, [$($body: expr),*]) => {
            ShiftedRule::new(
                Some(atom!($head)),
                Conjunction::from_iter([$($body),*])
            )
        };
    }

    macro_rules! crule {
        ([], [$([$($conj: expr),*]),*]) => {
            CompleteRule::new(
                None,
                Disjunction::from_iter([$(Conjunction::from_iter([$($conj),*])),*])
            )
        };
        ($pred: ident $(($($args: tt)*))?, [$([$($conj: expr),*]),*]) => {
            CompleteRule::new(
                Some(atom!($pred$(($($args)*))?)),
                Disjunction::from_iter([$(Conjunction::from_iter([$($conj),*])),*])
            )
        };
    }

    macro_rules! interp {
        ({$($x: tt),* $(,)?}) => {
            [$(atom!($x)),*].into_iter().collect::<Interpretation>()
        }
    }

    /// This program is already ground.
    #[test]
    fn ground_trivial_0() {
        let rules = [rule!([pos!(a), pos!(b), pos!(c)])];
        assert_eq!(
            Program::new(rules.clone()).ground().as_slice(),
            [rule!([pos!(a), pos!(b), pos!(c)]).ground()]
        );
    }

    /// This program needs a bit of grounding.
    #[test]
    fn ground_trivial_1() {
        let rules = [rule!([pos!(p(var!(x)))], [pos!(p(1)), pos!(p(2))])];
        assert_eq!(
            Program::new(rules).ground().as_slice(),
            [
                rule!([pos!(p(1))], [pos!(p(1)), pos!(p(2))]).ground(),
                rule!([pos!(p(2))], [pos!(p(1)), pos!(p(2))]).ground(),
            ]
        );
    }

    /// And this one needs a bit more.
    #[test]
    fn ground_gelfond_lifschitz_5() {
        let rules = [
            rule!([pos!(p(1, 2))]),
            rule!(
                [pos!(q(var!(x)))],
                [pos!(p(var!(x), var!(y))), neg!(q(var!(y)))]
            ),
        ];
        assert_eq!(
            Program::new(rules).ground().as_slice(),
            [
                rule!([pos!(p(1, 2))]).ground(),
                rule!([pos!(q(1))], [pos!(p(1, 1)), neg!(q(1))]).ground(),
                rule!([pos!(q(1))], [pos!(p(1, 2)), neg!(q(2))]).ground(),
                rule!([pos!(q(2))], [pos!(p(2, 1)), neg!(q(1))]).ground(),
                rule!([pos!(q(2))], [pos!(p(2, 2)), neg!(q(2))]).ground(),
            ]
        );
    }

    #[test]
    fn normalize_constraint() {
        let mut images = rule!([], [pos!(p), pos!(q)]).ground().image();
        assert_eq!(images.len(), 1);
        assert_eq!(
            images.remove(0).normalize(),
            [nrule!([], [pos!(p), pos!(q)])]
        );
    }

    #[test]
    fn normalize_choice() {
        let mut images = rule![{ pos!(p) }].ground().image();
        assert_eq!(images.len(), 1);
        assert_eq!(
            images.remove(0).normalize(),
            [nrule!([pos!(p), neg!(p)], [])]
        );
    }

    #[test]
    fn normalize_choices() {
        let mut images = rule![{pos!(p), pos!(q), pos!(r)}].ground().image();
        assert_eq!(images.len(), 3);
        assert_eq!(
            images.remove(2).normalize(),
            [nrule!([pos!(r), neg!(r)], [])]
        );
        assert_eq!(
            images.remove(1).normalize(),
            [nrule!([pos!(q), neg!(q)], [])]
        );
        assert_eq!(
            images.remove(0).normalize(),
            [nrule!([pos!(p), neg!(p)], [])]
        );
    }

    #[test]
    fn shift_disjunctive_rule() {
        let n = nrule!([pos!(a), pos!(b), pos!(c)], [pos!(d), pos!(e)]);
        assert_eq!(
            n.shift(),
            [
                srule!(a, [pos!(d), pos!(e), neg!(b), neg!(c)]),
                srule!(b, [pos!(d), pos!(e), neg!(a), neg!(c)]),
                srule!(c, [pos!(d), pos!(e), neg!(a), neg!(b)]),
            ]
        );
    }

    #[test]
    fn shift_head_negation() {
        assert_eq!(nrule!([neg!(q)], []).shift(), [srule!([], [nneg!(q)])]);
        assert_eq!(
            nrule!([pos!(p), neg!(q)], []).shift(),
            [srule!(p, [nneg!(q)])]
        );
    }

    #[test]
    fn shift_double_head_negation() {
        assert_eq!(nrule!([nneg!(q)], []).shift(), [srule!([], [neg!(q)])]);
        assert_eq!(
            nrule!([pos!(p), nneg!(q)], []).shift(),
            [srule!(p, [neg!(q)])]
        );
    }

    #[test]
    fn complete_trivial_0() {
        let rules = [rule!([pos!(p)])];
        let complete = Program::new(rules).preprocess(Trace::none());
        assert_eq!(complete.into_iter().collect::<Vec<_>>(), [crule!(p, [[]])]);
    }

    #[test]
    fn complete_trivial_1() {
        let rules = [rule!([pos!(a)], [pos!(b)])];
        let complete = Program::new(rules).preprocess(Trace::none());
        assert_eq!(
            complete.into_iter().collect::<Vec<_>>(),
            [crule![a, [[pos!(b)]]]]
        );
    }

    #[test]
    fn complete_constraint() {
        let rules = [rule!([], [pos!(p), pos!(q)])];
        let complete = Program::new(rules).preprocess(Trace::none());
        assert_eq!(
            complete.into_iter().collect::<Vec<_>>(),
            [crule!([], [[pos!(p), pos!(q)]])]
        );
    }

    /// Dodaro, example 10.
    #[test]
    fn complete_dodaro_example_10() {
        let rules = [
            rule!([pos!(a), pos!(b)]),
            rule!([pos!(c), pos!(d)], [pos!(a)]),
        ];
        let complete = Program::new(rules).preprocess(Trace::none());
        assert_eq!(
            complete.into_iter().collect::<Vec<_>>(),
            [
                crule!(a, [[neg!(b)]]),
                crule!(b, [[neg!(a)]]),
                crule!(c, [[pos!(a), neg!(d)]]),
                crule!(d, [[pos!(a), neg!(c)]]),
            ]
        );
    }

    /// Alviano and Dodaro, "Completion of Disjunctive Logic Programs" (IJCAI-16).
    fn alviano_dodaro_example_1() -> Vec<BaseRule<Term>> {
        vec![
            rule!([pos!(a), pos!(b), pos!(c)]),
            rule!([pos!(b)], [pos!(a)]),
            rule!([pos!(c)], [neg!(a)]),
        ]
    }

    #[test]
    fn complete_alviano_dodaro_example_1() {
        let rules = alviano_dodaro_example_1();
        let complete = Program::new(rules).preprocess(Trace::none());
        assert_eq!(
            complete.into_iter().collect::<Vec<_>>(),
            [
                crule!(a, [[neg!(b), neg!(c)]]),
                crule!(b, [[neg!(a), neg!(c)], [pos!(a)]]),
                crule!(c, [[neg!(a), neg!(b)], [neg!(a)]]),
            ]
        );
    }

    /// Lifschitz, "ASP", §5.2.
    #[test]
    fn reduce_asp_5_2() {
        // Rules (5.1)-(5.4).
        let rules = [
            rule!([pos!(p)]),
            rule!([pos!(q)]),
            rule!([pos!(r)], [pos!(p), neg!(s)]),
            rule!([pos!(s)], [pos!(q)]),
        ];
        let complete = Program::new(rules).preprocess(Trace::none());
        assert_eq!(
            complete.iter().cloned().collect::<Vec<_>>(),
            [
                crule!(p, [[]]),
                crule!(q, [[]]),
                crule!(r, [[pos!(p), neg!(s)]]),
                crule!(s, [[pos!(q)]]),
            ]
        );

        // Reduct (5.10).
        let interp = interp!({p, q, s});
        let reduct = complete.clone().reduce(&interp);
        assert_eq!(
            reduct.into_iter().collect::<Vec<_>>(),
            [
                crule!(p, [[]]),
                crule!(q, [[]]),
                crule!(r, []),
                crule!(s, [[pos!(q)]]),
            ]
        );
        assert!(complete.eval(&interp));

        // Reduct (5.11).
        let interp = interp!({p, q});
        let reduct = complete.clone().reduce(&interp);
        assert_eq!(
            reduct.iter().cloned().collect::<Vec<_>>(),
            [
                crule!(p, [[]]),
                crule!(q, [[]]),
                crule!(r, [[pos!(p)]]),
                crule!(s, [[pos!(q)]]),
            ]
        );
        assert!(!reduct.eval(&interp));
    }

    #[test]
    fn reduce_alviano_dodaro_example_1() {
        let rules = alviano_dodaro_example_1();
        let program = Program::new(rules).preprocess(Trace::none());
        let interp = interp!({ c });
        let reduct = program.clone().reduce(&interp);
        assert_eq!(
            reduct.into_iter().collect::<Vec<_>>(),
            [crule!(a, []), crule!(b, [[pos!(a)]]), crule!(c, [[], []]),]
        );
        assert!(program.eval(&interp));
    }

    /// P ∨ ¬P
    fn excluded_middle() -> Vec<BaseRule<Term>> {
        vec![rule!([pos!(p), neg!(p)])]
    }

    #[test]
    fn complete_excluded_middle() {
        let rules = excluded_middle();
        let complete = Program::new(rules).preprocess(Trace::none());
        assert_eq!(
            complete.into_iter().collect::<Vec<_>>(),
            [crule!(p, [[nneg!(p)]])]
        );
    }

    /// Lifschitz, "ASP" §5.4.
    #[test]
    fn reduce_excluded_middle() {
        let rules = excluded_middle();
        let complete = Program::new(rules).preprocess(Trace::none());

        let interp = interp!({});
        let reduct = complete.clone().reduce(&interp);
        assert!(reduct.eval(&interp));
        assert_eq!(reduct.into_iter().collect::<Vec<_>>(), [crule!(p, [])]);

        let interp = interp!({ p });
        let reduct = complete.clone().reduce(&interp);
        assert!(reduct.eval(&interp));
        assert_eq!(reduct.into_iter().collect::<Vec<_>>(), [crule!(p, [[]])]);
    }
}
