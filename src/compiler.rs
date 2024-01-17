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
//! (2019 draft, but really anything & everything by Lifschitz is helpful)
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
// TODO: fancier methods, e.g., unfounded-free checks

use std::collections::HashSet;

use gray_codes::{InclusionExclusion, SetMutation};

use crate::formula::*;
use crate::semantics::*;
use crate::solver::*;
use crate::syntax::*;
use crate::tracer::*;

/// An interpretation (a set of atoms which are "true") that satisfy a program.
pub type AnswerSet = Interpretation;

/// Searching for an answer set may fail.
pub type AnswerResult = Result<AnswerSet, XccError<Atom, bool>>;

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
    program: CompleteProgram,
    solver: DancingCells<Atom, bool>,
    trace: Trace,
}

impl XccCompiler {
    pub fn new(
        rules: impl IntoIterator<Item = Rule>,
        trace: Trace,
    ) -> Result<Self, XccError<Atom, bool>> {
        let program = Program::new(rules);
        trace!(trace, "Preparing program:\n{}", program);

        let program = program.normalize().ground().complete();
        trace!(trace, "Compiling program:\n{}", program);

        let (items, options) = Self::compile(&program, trace);
        trace!(
            trace,
            "XCC Items: {{{}}}",
            items
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ")
        );
        trace!(
            trace,
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
    /// models of the program. We use the idea of Knuth's Exercise 7.2.2.1-(76c):
    /// our primary items are fresh atoms {rule_R} representing the rules {R},
    /// our secondary items are all other atoms {x, y, ...}, and our options are
    /// sets of the form {rule_R, x:bool, y:bool, ...} for every combination
    /// of {x, y, ... ∈ R} that makes R true (i.e., local models of the rules).
    /// As Knuth notes, this is not a particularly efficient encoding (because
    /// it only gets one primary item per option), and we should try to improve
    /// on it (like looking for jointly (un)satisfying local models).
    fn compile(
        program: &CompleteProgram,
        _trace: Trace,
    ) -> (Items<Atom, bool>, Options<Atom, bool>) {
        let mut atoms = Interpretation::new();
        program.atoms(&mut atoms);
        let aux = (0..program.len())
            .map(|i| genaux("rule", i, &atoms))
            .collect::<AuxAtoms>();
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
            .collect::<Items<Atom, bool>>();

        let mut uniq = HashSet::<Items<Atom, bool>>::new();
        let options = program
            .iter()
            .zip(aux)
            .flat_map(|(rule, aux)| {
                // Encode rule-local models as XCC options. Secondary items (non-aux atoms) are
                // colored with their truth values (inclusion/exlusion) in the interpretation.
                let mut atoms = Interpretation::new();
                rule.atoms(&mut atoms);
                let atoms = atoms.into_iter().collect::<Vec<Atom>>();

                let maybe_make_option = |interp: &Interpretation| -> Option<Items<Atom, bool>> {
                    rule.eval(interp).then(|| {
                        [Item::Primary(aux.clone())]
                            .into_iter()
                            .chain(
                                atoms
                                    .iter()
                                    .map(|a| Item::Secondary(a.clone(), Some(interp.contains(a)))),
                            )
                            .collect()
                    })
                };

                // Look for local models by trying all possible interpretations
                // over the rule's atoms (via Gray codes), including the empty set.
                let mut interp = Interpretation::new();
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
                    .collect::<Options<Atom, bool>>()
            })
            .filter(|option| uniq.insert(option.clone())) // Oh, Rust!
            .collect::<Options<Atom, bool>>();
        (items, options)
    }

    /// Use the compiler to solve the reduct of a program w/r/t a model
    /// (previously found) of the full problem.
    fn is_stable_model(
        program: CompleteProgram,
        model: &Interpretation,
        trace: Trace,
    ) -> Result<bool, XccError<Atom, bool>> {
        let reduct = program.reduce(model);
        trace!(trace, "Reduct w/r/t {}:\n{}", format_answer(model), reduct);
        assert!(reduct.is_definite(), "reducts are definite by definition");

        let (items, options) = Self::compile(&reduct, trace);
        let solver = DancingCells::new(items, options, trace)?;
        if let Some(result) = AnswerStep::new(&reduct, solver.solve(), trace).next() {
            match result {
                Err(error) => Err(error),
                Ok(answer) => {
                    let stable = answer == *model;
                    trace!(
                        trace,
                        "Got answer {} to reduct; model is{} stable",
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

/// A definite program has a unique minimal model. We should probably
/// set up & solve a slightly different problem to find it, but for
/// now we'll just grab all the solutions and pick the minimal element
/// (the one that has no other models as a subset). For non-definite
/// programs (ones that involve negation), we must check each model
/// for stability.
pub enum Answer<'a> {
    UniqueModel(Option<DanceStep<'a, Atom, bool>>),
    StableModels(DanceStep<'a, Atom, bool>),
}

pub struct AnswerStep<'a> {
    program: &'a CompleteProgram,
    answer: Answer<'a>,
    trace: Trace,
}

impl<'a> AnswerStep<'a> {
    pub fn new(
        program: &'a CompleteProgram,
        step: DanceStep<'a, Atom, bool>,
        trace: Trace,
    ) -> Self {
        Self {
            program,
            answer: if program.is_definite() {
                Answer::UniqueModel(Some(step))
            } else {
                Answer::StableModels(step)
            },
            trace,
        }
    }

    /// Construct a model of the program from a solution of the XCC problem.
    fn answer(program: &CompleteProgram, solution: Options<Atom, bool>) -> AnswerSet {
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
            Answer::UniqueModel(ref mut step) => step.take().and_then(|step| {
                match step
                    .map(|r| r.map(|s| Self::answer(self.program, s)))
                    .collect::<Result<Vec<AnswerSet>, XccError<Atom, bool>>>()
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
            [$(atom![$head$(($($arg),*))?]),*]
                .into_iter()
                .collect::<AnswerSet>()
        }
    }

    macro_rules! assert_answers {
        ($answers:expr, [$({$($head:ident$(($($arg:tt),*))?),*}),* $(,)?]) => {
            let expected = [$(answer_set!{$($head$(($($arg),*))?),*}),*];
            assert!($answers == expected,
                    "Expected answer sets {{{}}}, got {{{}}}",
                    expected.iter().map(format_answer).collect::<Vec<_>>().join(", "),
                    $answers.iter().map(format_answer).collect::<Vec<_>>().join(", "));
        }
    }

    #[test]
    fn trivial_0() {
        assert!(matches!(
            XccCompiler::new([], false),
            Err(XccError::NoOptions)
        ));
    }

    #[test]
    fn trivial_1() {
        let rules = [rule![p]];
        let xcc = XccCompiler::new(rules, false).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ p }]);
    }

    #[test]
    fn trivial_2() {
        let rules = [rule![p if q], rule![q]];
        let xcc = XccCompiler::new(rules, false).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{p, q}]);
    }

    #[test]
    fn circular_1() {
        let rules = [rule![p if p]];
        let xcc = XccCompiler::new(rules, false).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{}]);
    }

    /// Lifschitz, "From Felicitous Models to Answer Set Programming", §3.
    #[test]
    fn felicitous_3() {
        let rules = [rule![p], rule![q if p], rule![r if q and s]];
        let xcc = XccCompiler::new(rules, false).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{p, q}]);
    }

    /// Lifschitz, "ASP", exercise 4.3.
    #[test]
    fn asp_4_3() {
        let rules = [rule![p if q and r], rule![q if p], rule![r if p]];
        let xcc = XccCompiler::new(rules, false).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{}]);
    }

    /// Lifschitz, "ASP", exercise 4.13.
    #[test]
    fn asp_4_13() {
        let rules = [rule![p or q], rule![r if p], rule![s if q]];
        let xcc = XccCompiler::new(rules, false).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{p, r}, {q, s}]);
    }

    /// Lifschitz, "ASP", §5.1.
    #[test]
    fn asp_5_1() {
        // Rules (5.1)-(5.4).
        let rules = [rule![p], rule![q], rule![r if p and not s], rule![s if q]];
        let xcc = XccCompiler::new(rules, false).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{p, q, s}]);

        // Rules (5.1)-(5.3).
        let rules = [rule![p], rule![q], rule![r if p and not s]];
        let xcc = XccCompiler::new(rules, false).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{p, q, r}]);

        // Rules (5.1),(5.3),(5.4) (exercise 5.1).
        let rules = [rule![p], rule![r if p and not s], rule![s if q]];
        let xcc = XccCompiler::new(rules, false).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{p, r}]);
    }

    /// Lifschitz, "ASP", §5.1.
    #[test]
    fn asp_5_2() {
        // Rules (5.6),(5.7).
        let rules = [rule![p if not q], rule![q if not r]];
        let xcc = XccCompiler::new(rules, false).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ q }]);
    }

    /// Lifschitz, "ASP", §5.1.
    #[test]
    fn asp_5_8() {
        // Rules (5.8),(5.9).
        let rules = [rule![p if not q], rule![q if not p]];
        let xcc = XccCompiler::new(rules, false).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ p }, { q }]);
    }

    #[test]
    fn unsatisfiable() {
        let rules = [rule![p if q], rule![q], rule![if p]];
        let xcc = XccCompiler::new(rules, false).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], []);
    }

    #[test]
    fn alviano_dodaro_example_1() {
        let rules = [rule![a or b or c], rule![b if a], rule![c if not a]];
        let xcc = XccCompiler::new(rules, false).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ c }]);
    }

    /// Gelfond & Lifschitz, program (5).
    #[test]
    fn gelfond_lifschitz_5() {
        let rules = [rule![p(a, b)], rule![q(X) if p(X, Y) and not q(Y)]];
        let xcc = XccCompiler::new(rules, false).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{ p(a, b), q(a) }]);
    }

    /// Gelfond & Lifschitz, program (5), remark 3.
    #[test]
    fn gelfond_lifschitz_5_3() {
        let rules = [
            rule![p(a, b)],
            rule![p(b, a)],
            rule![q(X) if p(X, Y) and not q(Y)],
        ];
        let xcc = XccCompiler::new(rules, false).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [
            { p(a, b), p(b, a), q(b) },
            { p(a, b), p(b, a), q(a) },
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
        let xcc = XccCompiler::new(rules, false).unwrap();
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
        let xcc = XccCompiler::new(rules, false).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(
            answers[..],
            [{motive(harry), motive(sally), guilty(harry), innocent(sally)}]
        );
    }
}
