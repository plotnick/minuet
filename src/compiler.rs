//! Map a logic program into an XCC problem, solve the problem,
//! then map the solutions back to program space.
//!
//! We use a simple encoding of the (normalized, completed) program
//! in XCC problem space based on Knuth's Exercise 7.2.2.1-(76c).
//! Translating solutions back into problem space yields (supported)
//! _models_ of the program.
//!
//! But not all of those models are necessarily _stable models_, i.e.,
//! _answer sets_; see Gelfond & Lifschitz "The Stable Model Semantics
//! for Logic Programming" (1988), Lifschitz "Answer Set Programming"
//! (2019 draft; but anything & everything by Lifschitz is helpful),
//! Dodaro's dissertation "Computational Tasks in Answer Set Programming"
//! (2013) and his work with Alviano et al., etc.
//!
//! Positive programs (ones without negation) have a unique minimal model
//! that is trivially stable, and we can find it by searching the models
//! that the solver returns for the smallest one (ordered by inclusion).
//! For programs with negation, the problem is somewhat harder. We can
//! compute the _reduct_ of the program with respect to a proposed model,
//! and find the minimal model of the reduced (positive) program; if that
//! model agrees with the proposed one, then the model is stable (this is
//! the semantics of Gelfond & Lifschitz).
//!
//! Checking for stability via reducts can be expensive, and for certain
//! classes of programs, it is possible to do better (see e.g., Dodaro's
//! dissertation). But we don't have those fancier checks yet.
//!
//! TODO: fancier methods, e.g., unfounded-free checks.

use std::collections::BTreeSet;

use gray_codes::{InclusionExclusion, SetMutation};

use minuet_syntax::*;
use minuet_tracer::*;

use crate::formula::*;
use crate::ground::*;
use crate::semantics::*;
use crate::solver::*;

pub use crate::solver::XccError; // re-export

/// A stable model of the program (Gelfond & Lifschitz 1988).
pub type AnswerSet = Model;

/// Searching for an answer set may fail.
pub type AnswerResult = Result<AnswerSet, XccError<Atom<GroundTerm>, bool>>;

pub fn format_answer(answer: &AnswerSet) -> String {
    format!(
        "{{{}}}",
        answer
            .iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>()
            .join(", ")
    )
}

pub struct XccCompiler {
    program: Program<CompleteRule>,
    solver: DancingCells<Atom<GroundTerm>, bool>,
    trace: Trace,
}

impl XccCompiler {
    pub fn new(
        rules: impl IntoIterator<Item = BaseRule<Term>>,
        trace: Trace,
    ) -> Result<Self, XccError<Atom<GroundTerm>, bool>> {
        let program = Program::<BaseRule<Term>>::new(rules);
        trace!(trace, Compile, "Preparing program:\n{}", program);

        let program = program.preprocess(trace);
        trace!(trace, Compile, "Compiling program:\n{}", program);

        let (items, options) = Self::compile(&program, trace);
        let solver = DancingCells::new(items, options, trace)?;
        Ok(Self {
            program,
            solver,
            trace,
        })
    }

    pub fn run(&self) -> AnswerStep {
        AnswerStep::new(&self.program, self.solver.solve(), self.trace)
    }

    /// Turn a normalized, grounded, completed program into an exact cover problem
    /// whose solutions are in 1-1 correspondence with the (not necessarily stable)
    /// models of that program. We use the idea of Knuth's Exercise 7.2.2.1-(76c):
    /// our primary items are fresh atoms {rule_R} representing the rules {R},
    /// our secondary items are all other atoms {x, y, ...}, and our options
    /// are sets of the form {rule_R, x:bool, y:bool, ...} for every combination
    /// of {x, y, ... ∈ R} that makes R true (i.e., local models of the rules).
    /// As Knuth notes, this is not a particularly efficient encoding (because
    /// it only gets one primary item per option), and we should try to improve
    /// on it (like looking for jointly (un)satisfying local models).
    fn compile(
        program: &Program<CompleteRule>,
        trace: Trace,
    ) -> (
        Items<Atom<GroundTerm>, bool>,
        Options<Atom<GroundTerm>, bool>,
    ) {
        let mut atoms = Interpretation::new();
        program.atoms(&mut atoms);
        let aux = (0..program.len())
            .map(|i| Atom::aux(Symbol::from("rule"), i))
            .collect::<Vec<_>>();
        assert_eq!(aux.len(), program.len());

        let mut secondary = atoms
            .into_iter()
            .map(|a| Item::Secondary(a, None))
            .collect::<Vec<_>>();
        secondary.sort_by_key(|i| i.name());

        let items = aux
            .iter()
            .cloned()
            .map(Item::Primary)
            .chain(secondary)
            .collect::<Items<Atom<GroundTerm>, bool>>();

        let options =
            program
                .iter()
                .zip(aux)
                .flat_map(|(rule, aux)| {
                    // Encode rule-local models as XCC options. Secondary items (non-aux atoms) are
                    // colored with their truth values (inclusion/exlusion) in the interpretation.
                    let mut atoms = Interpretation::new();
                    rule.atoms(&mut atoms);
                    let atoms = atoms.into_iter().collect::<Vec<Atom<GroundTerm>>>();

                    // Look for local models by trying all possible interpretations
                    // over the rule's atoms (via Gray codes), including the empty set.
                    let mut interp = Interpretation::new();
                    let maybe_make_option =
                        |interp: &Interpretation| -> Option<Items<Atom<GroundTerm>, bool>> {
                            rule.eval(interp).then(|| {
                                [Item::Primary(aux.clone())]
                                    .into_iter()
                                    .chain(atoms.iter().map(|a| {
                                        Item::Secondary(a.clone(), Some(interp.contains(a)))
                                    }))
                                    .collect()
                            })
                        };
                    if atoms.is_empty() {
                        maybe_make_option(&interp)
                            .into_iter()
                            .collect::<Options<Atom<GroundTerm>, bool>>()
                    } else {
                        maybe_make_option(&interp)
                            .into_iter()
                            .chain(
                                InclusionExclusion::of_len(atoms.len()).filter_map(|mutation| {
                                    match mutation {
                                        SetMutation::Insert(i) => interp.insert(atoms[i].clone()),
                                        SetMutation::Remove(i) => interp.remove(&atoms[i]),
                                    };
                                    maybe_make_option(&interp)
                                }),
                            )
                            .collect::<Options<Atom<GroundTerm>, bool>>()
                    }
                })
                .collect::<BTreeSet<Items<Atom<GroundTerm>, bool>>>()
                .into_iter()
                .collect::<Options<Atom<GroundTerm>, bool>>();

        trace!(
            trace,
            Compile,
            "XCC Items: {{{}}}",
            items
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ")
        );
        trace!(
            trace,
            Compile,
            "XCC Options: {{\n  {}\n}}\n",
            options
                .iter()
                .map(|o| format!(
                    "{{{}}}",
                    o.iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(", ")
                ))
                .collect::<Vec<_>>()
                .join(",\n  ")
        );
        (items, options)
    }

    /// Use the compiler to solve the reduct of a program w/r/t a model
    /// (previously found) of the full problem.
    fn is_stable_model(
        program: Program<CompleteRule>,
        model: &Model,
        trace: Trace,
    ) -> Result<bool, XccError<Atom<GroundTerm>, bool>> {
        let reduct = program.reduce(model);
        trace!(
            trace,
            Compile,
            "Reduct w/r/t {}:\n{}",
            format_answer(model),
            reduct
        );
        assert!(reduct.is_positive(), "reducts are positive by definition");

        let (items, options) = Self::compile(&reduct, trace);
        let solver = DancingCells::new(items, options, trace)?;
        if let Some(result) = AnswerStep::new(&reduct, solver.solve(), trace).next() {
            match result {
                Err(error) => Err(error),
                Ok(answer) => {
                    let stable = answer == *model;
                    trace!(
                        trace,
                        Compile,
                        "Got answer {} to reduced program; model is{} stable",
                        format_answer(&answer),
                        if stable { "" } else { " not" },
                    );
                    Ok(stable)
                }
            }
        } else {
            Ok(false)
        }
    }
}

/// An empty program has a trivial model. A non-empty positive program
/// has a unique minimal model; we should probably set up & solve a
/// slightly different problem to find it, but for now we'll just grab
/// all the solutions and pick the minimal element (the one that has no
/// other models as a subset). For non-positive programs (ones with negation),
/// we must check each model for stability. We use `Option::take` on the
/// first two to ensure we yield an answer just once.
#[derive(Debug)]
pub enum Answer<'a> {
    TrivialModel(Option<AnswerSet>),
    UniqueModel(Option<DanceStep<'a, Atom<GroundTerm>, bool>>),
    StableModels(DanceStep<'a, Atom<GroundTerm>, bool>),
}

pub struct AnswerStep<'a> {
    program: &'a Program<CompleteRule>,
    answer: Answer<'a>,
    trace: Trace,
}

impl<'a> AnswerStep<'a> {
    pub fn new(
        program: &'a Program<CompleteRule>,
        step: DanceStep<'a, Atom<GroundTerm>, bool>,
        trace: Trace,
    ) -> Self {
        Self {
            program,
            answer: if program.is_empty() {
                Answer::TrivialModel(Some(AnswerSet::new()))
            } else if program.is_positive() {
                Answer::UniqueModel(Some(step))
            } else {
                Answer::StableModels(step)
            },
            trace,
        }
    }

    /// Construct a model of the program from a solution of the XCC problem.
    fn answer(
        program: &Program<CompleteRule>,
        solution: Options<Atom<GroundTerm>, bool>,
    ) -> AnswerSet {
        let mut answer = AnswerSet::new();
        for option in solution {
            for item in option {
                if let Item::Secondary(atom, Some(true)) = item {
                    answer.insert(atom);
                }
            }
        }
        assert!(
            program.eval(&answer),
            "{} isn't a model of the program",
            format_answer(&answer),
        );
        answer
    }
}

impl<'a> Iterator for AnswerStep<'a> {
    type Item = AnswerResult;

    fn next(&mut self) -> Option<Self::Item> {
        match self.answer {
            Answer::TrivialModel(ref mut model) => model.take().map(Result::Ok),
            Answer::UniqueModel(ref mut step) => step.take().and_then(|step| {
                match step
                    .map(|r| r.map(|s| Self::answer(self.program, s)))
                    .collect::<Result<Vec<AnswerSet>, XccError<Atom<GroundTerm>, bool>>>()
                {
                    Err(error) => Some(Err(error)),
                    Ok(answers) if answers.is_empty() => None,
                    Ok(answers) => Some(Ok(answers
                        .iter()
                        .find(|&a| answers.iter().all(|b| b == a || !b.is_subset(a)))
                        .cloned()
                        .expect("can't find a unique model of the program"))),
                }
            }),
            Answer::StableModels(ref mut step) => {
                for result in step {
                    match result {
                        Err(error) => return Some(Err(error)),
                        Ok(solution) => {
                            let answer = Self::answer(self.program, solution);
                            match XccCompiler::is_stable_model(
                                self.program.clone(),
                                &answer,
                                self.trace,
                            ) {
                                Err(error) => return Some(Err(error)),
                                Ok(stable) if stable => return Some(Ok(answer)),
                                Ok(_unstable) => continue,
                            }
                        }
                    }
                }
                None
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! answer_set {
        {$($head:ident$(($($arg:tt),*))?),*} => {
            [$(atom![$head$(($($arg),*))?].ground()),*]
                .into_iter()
                .collect::<AnswerSet>()
        }
    }

    macro_rules! assert_answers {
        ($answers:expr, [$({$($head:ident$(($($arg:tt),*))?),* $(,)?}),* $(,)?]) => {{
            let expected = [$(answer_set!{$($head$(($($arg),*))?),*}),*];
            assert!($answers == expected,
                    "Expected answer sets:\n  [{}]\nGot answer sets:\n  [{}]",
                    expected.iter().map(format_answer).collect::<Vec<_>>().join(", "),
                    $answers.iter().map(format_answer).collect::<Vec<_>>().join(", "));
        }}
    }

    #[test]
    fn trivial_0() {
        let xcc = XccCompiler::new([], Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{}]);
    }

    #[test]
    fn trivial_1() {
        let rules = [rule![p]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ p }]);
    }

    #[test]
    fn trivial_2() {
        let rules = [rule![p if q], rule![q]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{p, q}]);
    }

    #[test]
    fn arg_0() {
        let rules = [rule![p()]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ p }]);
    }

    #[test]
    fn arg_1() {
        let rules = [rule![p(1)]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ p(1) }]);
    }

    #[test]
    fn arg_2() {
        let rules = [rule![p(1, 2)]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ p(1, 2) }]);
    }

    #[test]
    fn constraint_1() {
        let rules = [rule![if p]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{}]);
    }

    #[test]
    fn circular_1() {
        let rules = [rule![p if p]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{}]);
    }

    #[test]
    fn disjunctive_1() {
        let rules = [rule![p or p]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ p }]);
    }

    #[test]
    fn disjunctive_2() {
        let rules = [rule![p or q]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ q }, { p }]);
    }

    #[test]
    fn relational_0() {
        let rules = [rule![0 != 0]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], []);
    }

    #[test]
    fn relational_1() {
        let rules = [rule![1 = 1]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{}]);
    }

    #[test]
    fn relational_2() {
        let rules = [rule![0 = 1 or 1 = 1]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{}]);
    }

    #[test]
    fn arithmetic_0() {
        let rules = [rule![((0 + 0) = 1)]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], []);
    }

    #[test]
    fn arithmetic_1() {
        let rules = [rule![((1 + 1) = 2)]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{}]);
    }

    #[test]
    fn arithmetic_1a() {
        let rules = [rule![((|(-1)|) = 1)]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{}]);
    }

    #[test]
    fn arithmetic_1s() {
        let rules = [rule![((foo + bar) = foobar)]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{}]);
    }

    #[test]
    fn arithmetic_2() {
        let rules = [rule![((2 - 1) = 1)]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{}]);
    }

    #[test]
    fn arithmetic_2s() {
        let rules = [rule![((foobar - bar) = foo)]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{}]);
    }

    #[test]
    fn arithmetic_3() {
        let rules = [rule![(0 = (1 + 1)) or (1 = (2 - 2)) or (3 = (3 + 0))]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{}]);
    }

    #[test]
    fn arithmetic_4() {
        let rules = [rule![p((2 + 2))]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ p(4) }]);
    }

    #[test]
    fn interval_0() {
        let rules = [rule![q(0..0)]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ q(0) }]);
    }

    #[test]
    fn interval_1() {
        let rules = [rule![q(1..5)]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ q(1), q(2), q(3), q(4), q(5) }]);
    }

    #[test]
    fn interval_2() {
        let rules = [rule![q((1..3), (1..3))]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(
            answers[..], [{
                q(1, 1), q(1, 2), q(1, 3),
                q(2, 1), q(2, 2), q(2, 3),
                q(3, 1), q(3, 2), q(3, 3),
            }]
        );
    }

    #[test]
    fn interval_3() {
        let rules = [rule![q(((1..3) - (1..3)))]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ q((-2)), q((-1)), q(0), q(1), q(2) }]);
    }

    #[test]
    fn choice_1() {
        let rules = [rule![{ p }]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{}, { p }]);
    }

    #[test]
    fn choice_2() {
        let rules = [rule![{ p or q }]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{}, { q }, { p, q }, { p }]);
    }

    #[test]
    fn choice_3() {
        let rules = [rule![{ p or q or r }]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{}, { r }, { q, r }, { q }, { p, q }, { p }, { p, r }, {p, q, r}]);
    }

    #[test]
    fn choice_4a() {
        let rules = [rule![{p(1 or 2)}]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [
            {},
            {p(2)},
            {p(1), p(2)},
            {p(1)},
        ]);
    }

    #[test]
    fn choice_4b() {
        let rules = [rule![{p(a or b, 1 or 2)}]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [
            {},
            {p(b, 2)},
            {p(b, 1), p(b, 2)},
            {p(b, 1)},
            {p(b, 1), p(a, 2)},
            {p(a, 2)},
            {p(a, 2), p(b, 2)},
            {p(a, 2), p(b, 1), p(b, 2)},
            {p(a, 2), p(b, 1), p(b, 2), p(a, 1)},
            {p(a, 1), p(a, 2), p(b, 1)},
            {p(a, 1), p(b, 1)},
            {p(a, 1), p(b, 1), p(b, 2)},
            {p(a, 1), p(b, 2)},
            {p(a, 1), p(a, 2), p(b, 2)},
            {p(a, 1), p(a, 2)},
            {p(a, 1)},
        ]);
    }

    #[test]
    fn choice_4c() {
        let rules = [rule![{p(a or X, 1 or Y)} if (X = b) and (Y = 2)]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [
            {},
            {p(a, 2)},
            {p(a, 2), p(b, 1)},
            {p(b, 1)},
            {p(b, 1), p(b, 2)},
            {p(b, 2)},
            {p(a, 2), p(b, 2)},
            {p(a, 2), p(b, 1), p(b, 2)},
            {p(a, 1), p(a, 2), p(b, 1), p(b, 2)},
            {p(a, 1), p(b, 1), p(b, 2)},
            {p(a, 1), p(b, 1)},
            {p(a, 1), p(a, 2), p(b, 1)},
            {p(a, 1), p(a, 2)},
            {p(a, 1), p(a, 2), p(b, 2)},
            {p(a, 1), p(b, 2)},
            {p(a, 1)},
        ]);
    }

    /// Lifschitz, "ASP", §5.4. Also Aristotle, Shakespeare ("to p, or not p;
    /// that is the question"), etc.
    #[test]
    fn excluded_middle() {
        let rules = [rule![p or not p]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{}, { p }]);
    }

    #[test]
    fn unsatisfiable() {
        let rules = [rule![p if q], rule![q], rule![if p]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], []);
    }

    /// Lifschitz, "From Felicitous Models to Answer Set Programming", §3.
    #[test]
    fn felicitous_3() {
        let rules = [rule![p], rule![q if p], rule![r if q and s]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{p, q}]);
    }

    /// Lifschitz, "ASP", exercise 2.7.
    #[test]
    fn asp_2_7() {
        // Rule (2.7)
        let rules = [rule![p(N, ((N*N)+(N+41))) if N = (0..3)]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ p(0, 41), p(1, 43), p(2, 47), p(3, 53) }]);

        // Exercise 2.7 (a)
        let rules = [rule![p(N, ((N*N)+(N+41))) if ((N+1) = (1..4))]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ p(1, 43), p(2, 47), p(3, 53) }]);

        // Exercise 2.7 (b), same answer set as rule (2.7)
        let rules = [rule![p(N, ((N*N)+(N+41))) if (N = ((-3)..3)) and (N >= 0)]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ p(0, 41), p(1, 43), p(2, 47), p(3, 53) }]);
    }

    /// Lifschitz, "ASP", exercise 4.3.
    #[test]
    fn asp_4_3() {
        let rules = [rule![p if q and r], rule![q if p], rule![r if p]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{}]);
    }

    /// Lifschitz, "ASP", etc.
    #[test]
    fn asp_4_13() {
        let rules = [rule![p or q], rule![r if p], rule![s if q]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{q, s}, {p, r}]);
    }

    #[test]
    fn asp_4_34() {
        let rules = [rule![p(1)], rule![q if p(1..3)]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ p(1), q }]);
    }

    #[test]
    fn asp_5_1() {
        // Rules (5.1)-(5.4).
        let rules = [rule![p], rule![q], rule![r if p and not s], rule![s if q]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{p, q, s}]);

        // Rules (5.1)-(5.3).
        let rules = [rule![p], rule![q], rule![r if p and not s]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{p, q, r}]);

        // Rules (5.1),(5.3),(5.4) (exercise 5.1).
        let rules = [rule![p], rule![r if p and not s], rule![s if q]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{p, r}]);
    }

    #[test]
    fn asp_5_2() {
        // Rules (5.6),(5.7).
        let rules = [rule![p if not q], rule![q if not r]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ q }]);
    }

    #[test]
    fn asp_5_8() {
        // Rules (5.8),(5.9).
        let rules = [rule![p if not q], rule![q if not p]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ q }, { p }]);
    }

    #[test]
    fn asp_5_14() {
        let rules = [rule![p(a)], rule![q(b)], rule![r(X) if p(X) and not q(X)]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ p(a), q(b), r(a) }]);
    }

    #[test]
    fn asp_5_15() {
        let rules = [rule![p(1)], rule![q if not p(1..3)]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ p(1), q }]);
    }

    #[test]
    fn asp_5_17() {
        let rules = [rule![p(1..3)], rule![q(X) if (X = (2..4)) and not p(X)]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ p(1), p(2), p(3), q(4) }]);
    }

    #[test]
    fn asp_5_18() {
        let rules = [rule![p(1..4)], rule![q(X) if (X = (1..4)) and not p((X^2))]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ p(1), p(2), p(3), p(4), q(3), q(4) }]);
    }

    #[test]
    fn asp_5_19() {
        let rules = [rule![{ p(a) }], rule![q(X) if p(X)]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{}, { p(a), q(a) }]);
    }

    #[test]
    fn asp_5_20() {
        let rules = [rule![p(a)], rule![{q(X)} if p(X)]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ p(a), q(a) }, { p(a) }]);
    }

    #[test]
    fn asp_5_21() {
        let rules = [rule![0 {p(1..2, 1..2)} 2]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [
            {},
            {p(2, 2)},
            {p(2, 1), p(2, 2)},
            {p(2, 1)},
            {p(1, 2), p(2, 1)},
            {p(1, 2)},
            {p(1, 2), p(2, 2)},
            {p(1, 1), p(1, 2)},
            {p(1, 1)},
            {p(1, 1), p(2, 2)},
            {p(1, 1), p(2, 1)},
        ]);
    }

    #[test]
    fn asp_5_22() {
        let rules = [rule![2 {p(1..2, 1..2)} 2]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [
            {p(2, 1), p(2, 2)},
            {p(1, 2), p(2, 2)},
            {p(1, 2), p(2, 1)},
            {p(1, 1), p(2, 1)},
            {p(1, 1), p(2, 2)},
            {p(1, 1), p(1, 2)},
        ]);
    }

    #[test]
    fn asp_5_23() {
        // Example program (5.43).
        let rules = [
            rule![letter(a)],
            rule![letter(b)],
            rule![1 {p(X, 1..2)} 1 if letter(X)],
        ];

        let xcc = XccCompiler::new(rules.clone(), Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [
            {letter(a), letter(b), p(a, 1), p(b, 1)},
            {letter(a), letter(b), p(a, 1), p(b, 2)},
            {letter(a), letter(b), p(a, 2), p(b, 2)},
            {letter(a), letter(b), p(a, 2), p(b, 1)},
        ]);

        // Exercise 5.23.
        let ext_rules = rules.into_iter().chain([rule![{ p(c, 1) }]]);
        let xcc = XccCompiler::new(ext_rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [
            {letter(a), letter(b), p(a, 1), p(b, 1)},
            {letter(a), letter(b), p(a, 1), p(b, 1), p(c, 1)},
            {letter(a), letter(b), p(a, 1), p(b, 2), p(c, 1)},
            {letter(a), letter(b), p(a, 1), p(b, 2)},
            {letter(a), letter(b), p(a, 2), p(b, 2)},
            {letter(a), letter(b), p(a, 2), p(b, 2), p(c, 1)},
            {letter(a), letter(b), p(a, 2), p(b, 1), p(c, 1)},
            {letter(a), letter(b), p(a, 2), p(b, 1)},
        ]);
    }

    #[test]
    fn asp_5_35() {
        let rules = [rule![p if not q], rule![q if not r], rule![r if not p]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], []);
    }

    #[test]
    fn alviano_dodaro_example_1() {
        let rules = [rule![a or b or c], rule![b if a], rule![c if not a]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ c }]);
    }

    /// Gelfond & Lifschitz, program (5).
    #[test]
    fn gelfond_lifschitz_5() {
        let rules = [rule![p(1, 2)], rule![q(X) if p(X, Y) and not q(Y)]];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ p(1, 2), q(1) }]);
    }

    /// Gelfond & Lifschitz, program (5), remark 3.
    #[test]
    fn gelfond_lifschitz_5_3() {
        let rules = [
            rule![p(1, 2)],
            rule![p(2, 1)],
            rule![q(X) if p(X, Y) and not q(Y)],
        ];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [
            {p(1, 2), p(2, 1), q(1)},
            {p(1, 2), p(2, 1), q(2)},
        ]);
    }

    /// Gelfond & Lifschitz, program (6).
    #[test]
    fn gelfond_lifschitz_6() {
        let rules = [
            rule![p if q and not r],
            rule![q if r and not p],
            rule![r if p and not q],
        ];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{}]);
    }

    /// https://potassco.org/doc/start/
    #[test]
    fn potassco_start() {
        let rules = [
            rule![innocent(Suspect) if motive(Suspect) and not guilty(Suspect)],
            rule![motive(harry)],
            rule![motive(sally)],
            rule![guilty(harry)],
        ];
        let xcc = XccCompiler::new(rules, Trace::none()).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(
            answers[..],
            [{motive(harry), motive(sally), guilty(harry), innocent(sally)}]
        );
    }
}
