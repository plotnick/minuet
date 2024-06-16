//! A naïve, no-good strategy for grounding: bind every variable
//! to every possible constant value.

use minuet_syntax::*;

use super::{
    combinations_mixed, Bindings, Constants, GroundTerm, Groundable, Grounder, GroundingError,
    IsGround, Names, Safety, Universe, Value, Variables,
};

/// **DEAD DOVE! DO NOT EAT!**
///
/// Bind every variable in a program to every constant.
/// Should not to be used directly.
pub(crate) struct ExhaustiveGrounder {
    rules: Vec<BaseRule<Term>>,
}

impl ExhaustiveGrounder {
    pub(crate) fn new(rules: Vec<BaseRule<Term>>) -> Self {
        Self { rules }
    }
}

impl Grounder<Vec<BaseRule<Term>>> for ExhaustiveGrounder {
    /// Find all constants and bind all variables to them in all possible ways.
    /// Does not handle recursive symbolic functions at all. Importantly, produces
    /// many groundings that are not supported by the facts of the program.
    ///
    /// TODO: ground symbolic functions, inject initial bindings.
    fn ground(self, _bindings: &Bindings) -> Result<Vec<BaseRule<GroundTerm>>, GroundingError> {
        for rule in self.rules.iter() {
            rule.check_safety()?;
        }

        let constants = Vec::from_iter(self.rules.constants());
        let variables = Vec::from_iter(self.rules.variables());
        let (ground_rules, var_rules): (Vec<_>, Vec<_>) =
            self.rules.into_iter().partition(|r| r.is_ground());
        let mut rules = ground_rules
            .into_iter()
            .map(|rule| rule.ground().expect("rule should ground trivially"))
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
                    .map(|rule| rule.ground_with(&bindings))
                    .collect::<Result<Vec<_>, _>>()
                    .expect("can't ground rule"),
            );
        });

        rules.sort();
        rules.dedup();

        Ok(rules)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! xground {
        ($elt: expr) => {
            ExhaustiveGrounder::new($elt)
                .ground(&Bindings::new())
                .expect("exhaustive grounding failed")
        };
    }

    #[test]
    fn ground_0() {
        assert_eq!(
            xground!(vec![rule!([pos!(a(0))], [])]),
            xground!(vec![rule!([pos!(a(0))], [])]),
        );
    }

    #[test]
    fn ground_1() {
        assert_eq!(
            xground!(vec![rule!([pos!(a(x))], [rel!(x, Eq, 1)])]),
            xground!(vec![rule!([pos!(a(1))], [rel!(1, Eq, 1)])]),
        );
    }

    #[test]
    fn ground_2() {
        assert_eq!(
            xground!(vec![
                rule!([pos!(a(x))], [rel!(x, Eq, 1)]),
                rule!([pos!(a(x))], [rel!(x, Eq, 2)]),
            ]),
            xground!(vec![
                rule!([pos!(a(1))], [rel!(1, Eq, 1)]),
                rule!([pos!(a(1))], [rel!(1, Eq, 2)]),
                rule!([pos!(a(2))], [rel!(2, Eq, 1)]),
                rule!([pos!(a(2))], [rel!(2, Eq, 2)]),
            ]),
        );
    }
}
