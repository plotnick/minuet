//! Propositional images. See Lifschitz, "ASP".

use std::collections::BTreeSet;

use gray_codes::{InclusionExclusion, SetMutation};

use minuet_syntax::*;

use crate::clause::*;
use crate::ground::*;
use crate::values::*;

/// Propositional images of some expressions may be either conjunctive or
/// disjunctive, depending on whether they occur in the head or the body.
/// Other expressions have constant images (e.g., `2 + 2`), and may safely
/// ignore the context.
#[derive(Clone, Copy, Debug)]
pub enum Context {
    Head,
    Body,
}

impl Context {
    fn clause(self, elements: impl IntoIterator<Item = Clause>) -> Clause {
        match self {
            Self::Head => Clause::and(elements),
            Self::Body => Clause::or(elements),
        }
    }

    fn negate(self) -> Context {
        match self {
            Self::Head => Self::Body,
            Self::Body => Self::Head,
        }
    }
}

/// Part of a program projected into a propositional formula.
pub trait PropositionalImage {
    fn image(self, context: Context) -> Clause;
}

impl PropositionalImage for Aggregate<GroundTerm> {
    /// Lifschitz, "ASP" §5.7.
    fn image(self, context: Context) -> Clause {
        let Aggregate { choices, .. } = self;
        context.clause(
            choices
                .into_iter()
                .flat_map(|c| c.image(context))
                .map(|c| Clause::or([c.clone(), c.negate()])),
        )
    }
}

pub trait Bounds {
    fn bounds(self) -> Vec<Conjunction<Clause>>;
}

impl Bounds for Aggregate<GroundTerm> {
    /// Conjunctive constraints carrying cardinality bounds on an aggregate.
    /// See "ASP" §5.7, "AG" §4.7.
    fn bounds(self) -> Vec<Conjunction<Clause>> {
        match self {
            Aggregate {
                choices,
                bounds:
                    Some(AggregateBounds {
                        lower_bound,
                        upper_bound,
                    }),
            } => {
                let choices = choices
                    .into_iter()
                    .flat_map(|c| c.image(Context::Head))
                    .collect::<Vec<_>>();
                let upper_bound = upper_bound.values();
                let lower_bound = lower_bound.values();
                let mut formulas = BTreeSet::new();
                let mut lower = Vec::new();
                let mut bounds = Vec::new();
                for mutation in InclusionExclusion::of_len(choices.len()) {
                    match mutation {
                        SetMutation::Insert(i) => formulas.insert(choices[i].clone()),
                        SetMutation::Remove(i) => formulas.remove(&choices[i]),
                    };
                    let n = Constant::from(formulas.len() as i64);
                    let n_minus_1 = (n.clone() - Constant::from(1)).expect("n - 1");
                    if upper_bound.contains(&n_minus_1) {
                        bounds.push(Conjunction::from_iter(formulas.clone()));
                    }
                    if lower_bound.contains(&n) {
                        lower.push(Clause::and(formulas.clone()).negate());
                    }
                }
                if !lower.is_empty() {
                    bounds.push(Conjunction::from_iter(lower));
                }
                bounds
            }
            _ => vec![],
        }
    }
}

impl PropositionalImage for Application<GroundTerm> {
    fn image(self, context: Context) -> Clause {
        let Application {
            predicate,
            arguments,
        } = self;
        context.clause(all_values(arguments).into_iter().map(|args| {
            Clause::Lit(Literal::Positive(Atom::app(
                predicate.clone(),
                args.into_iter()
                    .map(GroundTerm::Constant)
                    .collect::<Vec<GroundTerm>>(),
            )))
        }))
    }
}

impl PropositionalImage for Atom<GroundTerm> {
    fn image(self, context: Context) -> Clause {
        match self {
            Atom::Aux(..) => Clause::Lit(Literal::Positive(self)),
            Atom::Agg(agg) => agg.image(context),
            Atom::App(app) => app.image(context),
        }
    }
}

impl PropositionalImage for Literal<GroundTerm> {
    /// "ASP" tables 4.4 and 5.4.
    fn image(self, context: Context) -> Clause {
        match self {
            Literal::Positive(atom) => atom.image(context),
            Literal::Negative(atom) => atom.image(context.negate()).negate(),
            Literal::DoubleNegative(atom) => atom.image(context).negate().negate(),
            Literal::Relation(x, op, y) => match context {
                Context::Head => {
                    let mut result = Clause::t();
                    for_all_value_pairs(*x, *y, |_values, x, y| {
                        if !op.eval(x, y) {
                            result = Clause::f();
                            // TODO: "break"
                        }
                    });
                    result
                }
                Context::Body => {
                    let mut result = Clause::f();
                    for_all_value_pairs(*x, *y, |_values, x, y| {
                        if op.eval(x, y) {
                            result = Clause::t();
                            // TODO: "break"
                        }
                    });
                    result
                }
            },
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use minuet_tracer::Trace;

    use crate::program::{Program, PropositionalRule};

    #[test]
    fn atomic_image() {
        use Context::*;

        assert_eq!(
            atom![p].ground().image(Head),
            Clause::and([Clause::Lit(lit![p].ground())])
        );

        assert_eq!(
            atom![p(1)].ground().image(Head),
            Clause::and([Clause::Lit(lit![p(1)].ground())])
        );

        assert_eq!(
            atom![p(1..1)].ground().image(Head),
            Clause::and([Clause::Lit(lit![p(1)].ground())])
        );

        assert_eq!(
            atom![p(1..2)].ground().image(Head),
            Clause::and([
                Clause::Lit(lit![p(1)].ground()),
                Clause::Lit(lit![p(2)].ground())
            ])
        );

        assert_eq!(
            atom![p(1, 2)].ground().image(Head),
            Clause::and([Clause::Lit(lit![p(1, 2)].ground())])
        );

        assert_eq!(
            atom![p(1..2, 2..3)].ground().image(Head),
            Clause::and([
                Clause::Lit(lit![p(1, 2)].ground()),
                Clause::Lit(lit![p(1, 3)].ground()),
                Clause::Lit(lit![p(2, 2)].ground()),
                Clause::Lit(lit![p(2, 3)].ground()),
            ])
        );

        assert_eq!(
            atom![p(1..2, 2..3, 3..4)].ground().image(Head),
            Clause::and([
                Clause::Lit(lit![p(1, 2, 3)].ground()),
                Clause::Lit(lit![p(1, 2, 4)].ground()),
                Clause::Lit(lit![p(1, 3, 3)].ground()),
                Clause::Lit(lit![p(1, 3, 4)].ground()),
                Clause::Lit(lit![p(2, 2, 3)].ground()),
                Clause::Lit(lit![p(2, 2, 4)].ground()),
                Clause::Lit(lit![p(2, 3, 3)].ground()),
                Clause::Lit(lit![p(2, 3, 4)].ground()),
            ])
        );

        // Lifschitz, "ASP" §5.7, first example.
        assert_eq!(
            atom![{p(1) or q(1..3)}].ground().image(Head),
            Clause::and([
                Clause::or([
                    Clause::Lit(lit![p(1)].ground()),
                    Clause::Lit(lit![not p(1)].ground())
                ]),
                Clause::or([
                    Clause::Lit(lit![q(1)].ground()),
                    Clause::Lit(lit![not q(1)].ground())
                ]),
                Clause::or([
                    Clause::Lit(lit![q(2)].ground()),
                    Clause::Lit(lit![not q(2)].ground())
                ]),
                Clause::or([
                    Clause::Lit(lit![q(3)].ground()),
                    Clause::Lit(lit![not q(3)].ground())
                ]),
            ])
        );
    }

    #[test]
    fn asp_5_21() {
        assert_eq!(
            Program::new([rule![0 {p(1..2, 1..2)} 2]])
                .ground()
                .image(Trace::none()),
            Program::new([
                // (A.8)
                PropositionalRule {
                    head: Clause::or([
                        Clause::Lit(glit![p(1, 1)]),
                        Clause::Lit(glit![not p(1, 1)])
                    ]),
                    body: Clause::t(),
                },
                PropositionalRule {
                    head: Clause::or([
                        Clause::Lit(glit![p(1, 2)]),
                        Clause::Lit(glit![not p(1, 2)])
                    ]),
                    body: Clause::t(),
                },
                PropositionalRule {
                    head: Clause::or([
                        Clause::Lit(glit![p(2, 1)]),
                        Clause::Lit(glit![not p(2, 1)])
                    ]),
                    body: Clause::t(),
                },
                PropositionalRule {
                    head: Clause::or([
                        Clause::Lit(glit![p(2, 2)]),
                        Clause::Lit(glit![not p(2, 2)])
                    ]),
                    body: Clause::t(),
                },
                // (A.9)
                PropositionalRule {
                    head: Clause::f(),
                    body: Clause::and([
                        Clause::Lit(glit![p(1, 1)]),
                        Clause::Lit(glit![p(1, 2)]),
                        Clause::Lit(glit![p(2, 1)])
                    ])
                },
                PropositionalRule {
                    head: Clause::f(),
                    body: Clause::and([
                        Clause::Lit(glit![p(1, 1)]),
                        Clause::Lit(glit![p(2, 1)]),
                        Clause::Lit(glit![p(2, 2)]),
                    ])
                },
                PropositionalRule {
                    head: Clause::f(),
                    body: Clause::and([
                        Clause::Lit(glit![p(1, 2)]),
                        Clause::Lit(glit![p(2, 1)]),
                        Clause::Lit(glit![p(2, 2)])
                    ])
                },
                PropositionalRule {
                    head: Clause::f(),
                    body: Clause::and([
                        Clause::Lit(glit![p(1, 1)]),
                        Clause::Lit(glit![p(1, 2)]),
                        Clause::Lit(glit![p(2, 2)])
                    ])
                },
            ])
        );
    }

    #[test]
    fn asp_5_22() {
        assert_eq!(
            Program::new([rule![2 {p(1..2, 1..2)} 2]])
                .ground()
                .image(Trace::none()),
            Program::new([
                // (A.8)
                PropositionalRule {
                    head: Clause::or([
                        Clause::Lit(glit![p(1, 1)]),
                        Clause::Lit(glit![not p(1, 1)])
                    ]),
                    body: Clause::t(),
                },
                PropositionalRule {
                    head: Clause::or([
                        Clause::Lit(glit![p(1, 2)]),
                        Clause::Lit(glit![not p(1, 2)])
                    ]),
                    body: Clause::t(),
                },
                PropositionalRule {
                    head: Clause::or([
                        Clause::Lit(glit![p(2, 1)]),
                        Clause::Lit(glit![not p(2, 1)])
                    ]),
                    body: Clause::t(),
                },
                PropositionalRule {
                    head: Clause::or([
                        Clause::Lit(glit![p(2, 2)]),
                        Clause::Lit(glit![not p(2, 2)])
                    ]),
                    body: Clause::t(),
                },
                // (A.9)
                PropositionalRule {
                    head: Clause::f(),
                    body: Clause::and([
                        Clause::Lit(glit![p(1, 1)]),
                        Clause::Lit(glit![p(1, 2)]),
                        Clause::Lit(glit![p(2, 1)])
                    ])
                },
                PropositionalRule {
                    head: Clause::f(),
                    body: Clause::and([
                        Clause::Lit(glit![p(1, 1)]),
                        Clause::Lit(glit![p(2, 1)]),
                        Clause::Lit(glit![p(2, 2)]),
                    ])
                },
                PropositionalRule {
                    head: Clause::f(),
                    body: Clause::and([
                        Clause::Lit(glit![p(1, 2)]),
                        Clause::Lit(glit![p(2, 1)]),
                        Clause::Lit(glit![p(2, 2)])
                    ])
                },
                PropositionalRule {
                    head: Clause::f(),
                    body: Clause::and([
                        Clause::Lit(glit![p(1, 1)]),
                        Clause::Lit(glit![p(1, 2)]),
                        Clause::Lit(glit![p(2, 2)])
                    ])
                },
                // (A.10)
                PropositionalRule {
                    head: Clause::f(),
                    body: Clause::and([
                        Clause::or([
                            Clause::Lit(glit![not p(1, 1)]),
                            Clause::Lit(glit![not p(1, 2)]),
                        ]),
                        Clause::or([
                            Clause::Lit(glit![not p(1, 2)]),
                            Clause::Lit(glit![not p(2, 1)]),
                        ]),
                        Clause::or([
                            Clause::Lit(glit![not p(1, 1)]),
                            Clause::Lit(glit![not p(2, 1)]),
                        ]),
                        Clause::or([
                            Clause::Lit(glit![not p(2, 1)]),
                            Clause::Lit(glit![not p(2, 2)]),
                        ]),
                        Clause::or([
                            Clause::Lit(glit![not p(1, 2)]),
                            Clause::Lit(glit![not p(2, 2)]),
                        ]),
                        Clause::or([
                            Clause::Lit(glit![not p(1, 1)]),
                            Clause::Lit(glit![not p(2, 2)]),
                        ]),
                    ])
                },
            ])
        );
    }
}
