//! Compositional clauses: formulas containing conjunctions & disjunctions.
//! Used to represent propositional images; see Lifschitz, "ASP" §§ 4.6-7.
//! The normalization routines were adapted from [Stuart Russel's beautiful
//! Common Lisp code](https://people.eecs.berkeley.edu/~russell/code/logic/algorithms/normal.lisp).
//!
//! TODO: Simplifier.

use std::fmt;
use std::ops::Index;
use std::vec;

use minuet_syntax::*;

use crate::ground::*;

/// Conjunction means _and_. It is spelled "∧" in propositional logic.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Conjunction<T>(Vec<T>);

impl<T> Conjunction<T> {
    /// The empty conjunction is _true_.
    pub fn t() -> Self {
        Self(Vec::new())
    }

    pub fn and_also(mut self, conjuncts: impl IntoIterator<Item = T>) -> Self {
        self.0.extend(conjuncts);
        self
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.0.iter()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl<T> Default for Conjunction<T> {
    fn default() -> Self {
        Self::t()
    }
}

impl<T> Index<usize> for Conjunction<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        self.0.index(index)
    }
}

impl<T> FromIterator<T> for Conjunction<T> {
    fn from_iter<I: IntoIterator<Item = T>>(conjuncts: I) -> Self {
        Self(conjuncts.into_iter().collect())
    }
}

impl<T> IntoIterator for Conjunction<T> {
    type Item = T;
    type IntoIter = vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T> fmt::Display for Conjunction<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            f.write_str("⊤")
        } else {
            let s = self
                .iter()
                .map(|c| c.to_string())
                .collect::<Vec<_>>()
                .join(" ∧ ");
            f.write_str(&s)
        }
    }
}

/// Disjunction means _or_. It is spelled "∨" in propositional logic.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Disjunction<T>(Vec<T>);

impl<T> Disjunction<T> {
    /// The empty disjunction is _false_.
    pub fn f() -> Self {
        Self(Vec::new())
    }

    pub fn or_else(mut self, disjuncts: impl IntoIterator<Item = T>) -> Self {
        self.0.extend(disjuncts);
        self
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.0.iter()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl<T> Default for Disjunction<T> {
    fn default() -> Self {
        Self::f()
    }
}

impl<T> Index<usize> for Disjunction<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        self.0.index(index)
    }
}

impl<T> FromIterator<T> for Disjunction<T> {
    fn from_iter<I: IntoIterator<Item = T>>(disjuncts: I) -> Self {
        Self(disjuncts.into_iter().collect())
    }
}

impl<T> IntoIterator for Disjunction<T> {
    type Item = T;
    type IntoIter = vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T> fmt::Display for Disjunction<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            f.write_str("⊥")
        } else {
            let s = self
                .iter()
                .map(|c| c.to_string())
                .collect::<Vec<_>>()
                .join(" ∨ ");
            f.write_str(&s)
        }
    }
}

/// A literal, conjunction, or disjunction of ground literals.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Clause {
    Lit(Literal<GroundTerm>),
    And(Conjunction<Clause>),
    Or(Disjunction<Clause>),
}

impl Clause {
    pub fn t() -> Self {
        Self::And(Conjunction::t())
    }

    pub fn and(conjuncts: impl IntoIterator<Item = Clause>) -> Self {
        Self::And(Conjunction::from_iter(conjuncts))
    }

    pub fn f() -> Self {
        Self::Or(Disjunction::f())
    }

    pub fn or(disjuncts: impl IntoIterator<Item = Clause>) -> Self {
        Self::Or(Disjunction::from_iter(disjuncts))
    }

    pub fn negate(self) -> Self {
        match self {
            Self::Lit(l) => Self::Lit(l.negate()),
            Self::And(c) => Self::or(c.into_iter().map(Self::negate)),
            Self::Or(d) => Self::and(d.into_iter().map(Self::negate)),
        }
    }

    pub fn is_positive(&self) -> bool {
        match self {
            Self::Lit(l) => l.is_positive(),
            Self::And(c) => c.iter().all(Self::is_positive),
            Self::Or(d) => d.iter().all(Self::is_positive),
        }
    }
}

impl IntoIterator for Clause {
    type Item = Clause;
    type IntoIter = vec::IntoIter<Clause>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Self::Lit(_) => vec![self].into_iter(),
            Self::And(c) => c.into_iter(),
            Self::Or(d) => d.into_iter(),
        }
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Lit(l) => l.to_string(),
            Self::And(c) => c.to_string(),
            Self::Or(d) => d.to_string(),
        };
        f.write_str(&s)
    }
}

/// Conjuctive normal form.
pub type Cnf = Conjunction<Disjunction<Literal<GroundTerm>>>;

/// Disjunctive normal form.
pub type Dnf = Disjunction<Conjunction<Literal<GroundTerm>>>;

impl Clause {
    /// Normalize to CNF.
    pub fn cnf(self) -> Cnf {
        match self {
            Self::Lit(l) => Conjunction::from_iter([Disjunction::from_iter([l])]),
            Self::And(c) => c
                .into_iter()
                .fold(Conjunction::default(), |cnf, c| cnf.and_also(c.cnf())),
            Self::Or(d) => merge_arguments(d.into_iter().map(Self::cnf).collect()),
        }
    }

    /// Normalize to DNF.
    pub fn dnf(self) -> Dnf {
        match self {
            Self::Lit(l) => Disjunction::from_iter([Conjunction::from_iter([l])]),
            Self::And(c) => merge_arguments(c.into_iter().map(Self::dnf).collect()),
            Self::Or(d) => d
                .into_iter()
                .fold(Disjunction::default(), |dnf, d| dnf.or_else(d.dnf())),
        }
    }
}

/// Helper for C/DNF conversion.
fn merge_arguments<F, G, X, Y>(mut args: Vec<F>) -> F
where
    F: IntoIterator<Item = X> + FromIterator<G> + Clone,
    G: IntoIterator<Item = Y> + FromIterator<Y> + Default,
    X: IntoIterator<Item = Y> + Clone,
{
    match args.len() {
        0 => F::from_iter([G::default()]),
        1 => args.pop().expect("args should be non-empty"),
        _ => F::from_iter(
            merge_arguments(args[1..].to_vec())
                .into_iter()
                .flat_map(|y| {
                    args[0]
                        .clone()
                        .into_iter()
                        .map(move |x| G::from_iter(x.into_iter().chain(y.clone())))
                }),
        ),
    }
}

impl Cnf {
    /// Turn CNF back into a clause (for conversion to DNF).
    fn clause(self) -> Clause {
        Clause::and(
            self.into_iter()
                .map(|x| Clause::or(x.into_iter().map(Clause::Lit))),
        )
    }

    /// Convert CNF → DNF
    pub fn dnf(self) -> Dnf {
        self.clause().dnf()
    }
}

impl Dnf {
    /// Turn DNF back into a clause (for conversion to CNF).
    fn clause(self) -> Clause {
        Clause::or(
            self.into_iter()
                .map(|x| Clause::and(x.into_iter().map(Clause::Lit))),
        )
    }

    /// Convert DNF → CNF
    pub fn cnf(self) -> Cnf {
        self.clause().cnf()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! clause {
        [] => { Clause::t() };
        [($($clause:tt)*)] => { clause![$($clause)*] };
        [$a:tt $(and $b:tt)+] => {
            Clause::and([clause![$a], $(clause![$b]),+])
        };
        [$a:tt $(or $b:tt)+] => {
            Clause::or([clause![$a], $(clause![$b]),+])
        };
        [not not $lit:tt] => {
            Clause::Lit(glit![not not $lit])
        };
        [not $lit:tt] => {
            Clause::Lit(glit![not $lit])
        };
        [$lit:tt] => {
            Clause::Lit(glit![$lit])
        };
    }

    #[test]
    fn clause() {
        let c = clause![a and b and c];
        let d = clause![x or y or z];
        let e = Clause::and([c, d]);
        assert_eq!(e, clause![(a and b and c) and (x or y or z)]);
    }

    fn test_clauses() -> (
        Clause,
        Clause,
        Clause,
        Clause,
        Clause,
        Clause,
        Clause,
        Clause,
        Clause,
    ) {
        (
            clause![],
            clause![p],
            clause![p and q],
            clause![p or q],
            clause![p and (q or r)],
            clause![p or (q and r)],
            clause![(not p) or (q and (r or (not s)))],
            clause![(q and r) or ((not q) and (a or b))],
            clause![(a or b) and ((c or d) and (e or f) and (g or h))],
        )
    }

    #[test]
    fn cnf() {
        let (c0, c1, c2, c3, c4, c5, c6, c7, c8) = test_clauses();
        assert_eq!(c0.cnf(), Cnf::t());
        assert_eq!(
            c1.cnf(),
            Cnf::from_iter([Disjunction::from_iter([glit![p]])])
        );
        assert_eq!(
            c2.cnf(),
            Cnf::from_iter([
                Disjunction::from_iter([glit![p]]),
                Disjunction::from_iter([glit![q]])
            ])
        );
        assert_eq!(
            c3.cnf(),
            Cnf::from_iter([Disjunction::from_iter([glit![p], glit![q]])])
        );
        assert_eq!(
            c4.cnf(),
            Cnf::from_iter([
                Disjunction::from_iter([glit![p]]),
                Disjunction::from_iter([glit![q], glit![r]]),
            ])
        );
        assert_eq!(
            c5.cnf(),
            Cnf::from_iter([
                Disjunction::from_iter([glit![p], glit![q]]),
                Disjunction::from_iter([glit![p], glit![r]]),
            ])
        );
        assert_eq!(
            c6.cnf(),
            Cnf::from_iter([
                Disjunction::from_iter([glit![not p], glit![q]]),
                Disjunction::from_iter([glit![not p], glit![r], glit![not s]])
            ])
        );
        assert_eq!(
            c7.cnf(),
            Cnf::from_iter([
                Disjunction::from_iter([glit![q], glit![not q]]),
                Disjunction::from_iter([glit![r], glit![not q]]),
                Disjunction::from_iter([glit![q], glit![a], glit![b]]),
                Disjunction::from_iter([glit![r], glit![a], glit![b]]),
            ])
        );
        assert_eq!(
            c8.cnf(),
            Cnf::from_iter([
                Disjunction::from_iter([glit![a], glit![b]]),
                Disjunction::from_iter([glit![c], glit![d]]),
                Disjunction::from_iter([glit![e], glit![f]]),
                Disjunction::from_iter([glit![g], glit![h]]),
            ])
        );
    }

    #[test]
    fn dnf() {
        let (c0, c1, c2, c3, c4, c5, c6, c7, c8) = test_clauses();
        assert_eq!(c0.dnf(), Dnf::from_iter([Conjunction::t()]));
        assert_eq!(
            c1.dnf(),
            Dnf::from_iter([Conjunction::from_iter([glit![p]])])
        );
        assert_eq!(
            c2.dnf(),
            Dnf::from_iter([Conjunction::from_iter([glit![p], glit![q]])])
        );
        assert_eq!(
            c3.dnf(),
            Dnf::from_iter([
                Conjunction::from_iter([glit![p]]),
                Conjunction::from_iter([glit![q]])
            ])
        );
        assert_eq!(
            c4.dnf(),
            Dnf::from_iter([
                Conjunction::from_iter([glit![p], glit![q]]),
                Conjunction::from_iter([glit![p], glit![r]]),
            ])
        );
        assert_eq!(
            c5.dnf(),
            Dnf::from_iter([
                Conjunction::from_iter([glit![p]]),
                Conjunction::from_iter([glit![q], glit![r]]),
            ])
        );
        assert_eq!(
            c6.dnf(),
            Dnf::from_iter([
                Conjunction::from_iter([glit![not p]]),
                Conjunction::from_iter([glit![q], glit![r]]),
                Conjunction::from_iter([glit![q], glit![not s]]),
            ])
        );
        assert_eq!(
            c7.dnf(),
            Dnf::from_iter([
                Conjunction::from_iter([glit![q], glit![r]]),
                Conjunction::from_iter([glit![not q], glit![a]]),
                Conjunction::from_iter([glit![not q], glit![b]]),
            ])
        );
        assert_eq!(
            c8.dnf(),
            Dnf::from_iter([
                Conjunction::from_iter([glit![a], glit![c], glit![e], glit![g]]),
                Conjunction::from_iter([glit![b], glit![c], glit![e], glit![g]]),
                Conjunction::from_iter([glit![a], glit![d], glit![e], glit![g]]),
                Conjunction::from_iter([glit![b], glit![d], glit![e], glit![g]]),
                Conjunction::from_iter([glit![a], glit![c], glit![f], glit![g]]),
                Conjunction::from_iter([glit![b], glit![c], glit![f], glit![g]]),
                Conjunction::from_iter([glit![a], glit![d], glit![f], glit![g]]),
                Conjunction::from_iter([glit![b], glit![d], glit![f], glit![g]]),
                Conjunction::from_iter([glit![a], glit![c], glit![e], glit![h]]),
                Conjunction::from_iter([glit![b], glit![c], glit![e], glit![h]]),
                Conjunction::from_iter([glit![a], glit![d], glit![e], glit![h]]),
                Conjunction::from_iter([glit![b], glit![d], glit![e], glit![h]]),
                Conjunction::from_iter([glit![a], glit![c], glit![f], glit![h]]),
                Conjunction::from_iter([glit![b], glit![c], glit![f], glit![h]]),
                Conjunction::from_iter([glit![a], glit![d], glit![f], glit![h]]),
                Conjunction::from_iter([glit![b], glit![d], glit![f], glit![h]]),
            ])
        );
    }

    #[test]
    #[ignore = "needs a simplifier"]
    fn cnf_dnf() {
        let (c0, c1, c2, c3, c4, c5, c6, c7, c8) = test_clauses();
        for c in [c0, c1, c2, c3, c4, c5, c6, c7, c8] {
            let cnf = c.clone().cnf();
            let dnf = c.clone().dnf();
            let cnf_dnf = cnf.clone().dnf();
            let dnf_cnf = dnf.clone().cnf();
            let cnf_dnf_cnf = cnf_dnf.cnf();
            let dnf_cnf_dnf = dnf_cnf.dnf();
            assert_eq!(cnf_dnf_cnf, cnf);
            assert_eq!(dnf_cnf_dnf, dnf);
        }
    }
}
