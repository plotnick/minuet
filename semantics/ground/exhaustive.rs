//! A simple strategy for grounding: bind every variable to every
//! possible value. It is not a good strategy, though.

use minuet_syntax::{BaseRule, Symbol, Term};

use crate::generate::combinations_mixed;
use crate::program::{BaseProgram, Program};
use crate::values::Value;

use super::{Bindings, Groundable, Grounder, Names, Universe};

/// **DEAD DOVE! DO NOT EAT!**
///
/// Bind every variable in a program to every constant.
/// Should not to be used directly.
pub(crate) struct ExhaustiveGrounder {
    program: BaseProgram,
}

impl ExhaustiveGrounder {
    pub(crate) fn new(program: BaseProgram) -> Self {
        Self { program }
    }
}

impl Grounder<BaseProgram> for ExhaustiveGrounder {
    /// Find all constants and bind all variables to them in all possible ways.
    /// Does not handle recursive symbolic functions at all. Importantly, produces
    /// many groundings that are not supported by the facts of the program.
    ///
    /// TODO: ground symbolic functions, inject initial bindings.
    fn ground(
        self,
        _bindings: &Bindings,
    ) -> Result<<BaseProgram as Groundable>::Ground, <BaseProgram as Groundable>::Error> {
        let mut constants = Universe::new();
        self.program.constants(&mut constants);
        let constants = constants.into_iter().collect::<Vec<Value>>();

        let mut variables = Names::new();
        self.program.variables(&mut variables);
        let variables = variables.into_iter().collect::<Vec<Symbol>>();

        let (ground_rules, var_rules): (Vec<_>, Vec<_>) =
            self.program.into_iter().partition(|r| r.is_ground());
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

        Ok(Program::new(rules))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use minuet_syntax::*;

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
            xground!(Program::new([rule!([pos!(a(0))], [])])),
            xground!(Program::new([rule!([pos!(a(0))], [])])),
        );
    }

    #[test]
    fn ground_1() {
        assert_eq!(
            xground!(Program::new([rule!([pos!(a(x))], [rel!(x, Eq, 1)])])),
            xground!(Program::new([rule!([pos!(a(1))], [rel!(1, Eq, 1)])])),
        );
    }

    #[test]
    fn ground_2() {
        assert_eq!(
            xground!(Program::new([
                rule!([pos!(a(x))], [rel!(x, Eq, 1)]),
                rule!([pos!(a(x))], [rel!(x, Eq, 2)]),
            ])),
            xground!(Program::new([
                rule!([pos!(a(1))], [rel!(1, Eq, 1)]),
                rule!([pos!(a(1))], [rel!(1, Eq, 2)]),
                rule!([pos!(a(2))], [rel!(2, Eq, 1)]),
                rule!([pos!(a(2))], [rel!(2, Eq, 2)]),
            ])),
        );
    }
}
