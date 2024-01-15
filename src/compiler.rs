//! Map a logic program into an XCC problem, solve the problem,
//! then map the solutions back to program space. Most of the
//! heavy lifting is done by the semantic transformations.

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

fn format_answer(answer: &AnswerSet) -> String {
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
}

impl XccCompiler {
    pub fn new(
        rules: impl IntoIterator<Item = Rule>,
        trace: Trace,
    ) -> Result<Self, XccError<Atom, bool>> {
        let program = Program::new(rules).normalize().ground().complete();
        let (items, options) = Self::compile(&program, trace);
        let solver = DancingCells::new(items, options, trace)?;
        Ok(Self { program, solver })
    }

    pub fn run(&self) -> AnswerStep {
        AnswerStep::new(&self.program, self.solver.solve())
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
        trace: Trace,
    ) -> (Items<Atom, bool>, Options<Atom, bool>) {
        trace!(trace, "Compiling complete program:\n{}", program);

        let atoms = program.uniq_atoms();
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
                let atoms = rule.atoms();
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
        (items, options)
    }
}

/// A definite program has a unique minimal model. We should probably
/// set up & solve a different problem to find it, but for now we'll
/// just accumulate all the solutions and pick the minimal element
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
}

impl<'a> AnswerStep<'a> {
    fn new(program: &'a CompleteProgram, step: DanceStep<'a, Atom, bool>) -> Self {
        Self {
            program,
            answer: if program.is_definite() {
                Answer::UniqueModel(Some(step))
            } else {
                Answer::StableModels(step)
            },
        }
    }

    /// Construct an answer set (a model of the program) from a solution
    /// of the XCC problem.
    fn answer(&self, solution: Options<Atom, bool>) -> AnswerSet {
        let mut answer = AnswerSet::new();
        for option in solution {
            for item in option {
                if let Item::Secondary(atom, Some(true)) = item {
                    answer.insert(atom);
                }
            }
        }
        assert!(
            self.program.eval(&answer),
            "{} isn't a model of the program",
            format_answer(&answer),
        );
        answer
    }

    /// Drive the solver to completion, then choose the unique minimal model.
    fn unique(&self, step: DanceStep<'a, Atom, bool>) -> Option<AnswerResult> {
        match step
            .map(|r| r.map(|s| self.answer(s)))
            .collect::<Result<Vec<AnswerSet>, XccError<Atom, bool>>>()
        {
            Ok(answers) if answers.is_empty() => None,
            Ok(answers) => Some(Ok(answers
                .iter()
                .find(|&a| answers.iter().all(|b| b == a || !b.is_subset(a)))
                .cloned()
                .expect("couldn't find a unique model of the program"))),
            Err(error) => Some(Err(error)),
        }
    }
}

impl<'a> Iterator for AnswerStep<'a> {
    type Item = AnswerResult;

    fn next(&mut self) -> Option<Self::Item> {
        match self.answer {
            Answer::UniqueModel(ref mut step) => step.take().and_then(|step| self.unique(step)),
            Answer::StableModels(ref mut step) => step.next().map(|r| r.map(|s| self.answer(s))),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! answer_set {
        {} => { AnswerSet::new() };
        {$($e:expr),+ $(,)?} => {{
            let mut set = AnswerSet::new();
            set.extend([$($e),+]);
            set
        }};
    }

    macro_rules! assert_answers {
        ($answers:expr, [$({$($e:expr),* $(,)?}),* $(,)?]) => {
            let expected = [$(answer_set!{$($e),*}),*];
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
        assert_answers!(answers[..], [{ atom![p] }]);
    }

    #[test]
    fn trivial_2() {
        let rules = [rule![p if q], rule![q]];
        let xcc = XccCompiler::new(rules, false).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{atom![p], atom![q]}]);
    }

    #[test]
    fn circular_1() {
        let rules = [rule![p if p]];
        let xcc = XccCompiler::new(rules, false).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{}]);
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
        assert_answers!(
            answers[..],
            [
                {atom![p], atom![r]},
                {atom![q], atom![s]},
            ]
        );
    }

    /// From §3 of Lifschitz, "From Felicitous Models to Answer Set Programming".
    #[test]
    fn felicitous_3() {
        let rules = [rule![a], rule![b if a], rule![d if b and c]];
        let xcc = XccCompiler::new(rules, false).unwrap();
        let answers = xcc.run().collect::<Result<Vec<_>, _>>().unwrap();
        assert_answers!(answers[..], [{atom![a], atom![b]}]);
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
        assert_answers!(answers[..], [{ atom![c] }]);
    }
}
