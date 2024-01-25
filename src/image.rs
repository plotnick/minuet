//! Propositional images. See Lifschitz, "ASP".

use crate::clause::*;
use crate::syntax::*;
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

/// Lifschitz, "ASP" §5.7.
impl PropositionalImage for Aggregate<GroundTerm> {
    fn image(self, context: Context) -> Clause {
        let Aggregate { choices } = self;
        context.clause(
            choices
                .into_iter()
                .flat_map(|c| c.image(context))
                .map(|c| Clause::or([c.clone(), c.negate()])),
        )
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

/// See "ASP" Tables 4.4 and 5.4.
impl PropositionalImage for Literal<GroundTerm> {
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
    use crate::formula::Groundable as _;

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
}
