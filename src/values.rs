//! Operations on sets of constant values. See "Abstract Gringo" §4.2
//! and Lifschitz, "ASP" §§ 4.6-7.
//!
//! Operations on sets of values ultimately boil down to operations on
//! individual constants, so we also implement the standard Rust arithmetic
//! traits on `Constant`. We currently allow arithmetic operations to mix
//! numbers and names (as strings); this may be a mistake. But all such
//! methods return `Option<Constant>`, so we don't need to define all
//! possible operations.

use std::cmp::Ordering;
use std::collections::btree_set::{self, BTreeSet};
use std::iter::FromIterator;
use std::ops::{self, Neg as _, Not as _};

use minuet_syntax::*;

use crate::generate::combinations_mixed;
use crate::ground::*;

/// A set of constant values denoted by some term.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValueSet(BTreeSet<Constant>);

impl ValueSet {
    pub fn new() -> Self {
        Self(BTreeSet::new())
    }

    pub fn contains(&self, c: &Constant) -> bool {
        self.0.contains(c)
    }

    pub fn insert(&mut self, c: Constant) {
        self.0.insert(c);
    }
}

impl Extend<Constant> for ValueSet {
    fn extend<Iter: IntoIterator<Item = Constant>>(&mut self, iter: Iter) {
        iter.into_iter().for_each(move |elem| {
            self.insert(elem);
        });
    }
}

impl FromIterator<Constant> for ValueSet {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Constant>,
    {
        Self(iter.into_iter().collect())
    }
}

impl IntoIterator for ValueSet {
    type Item = Constant;
    type IntoIter = btree_set::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

/// Compute and return the set of values denoted by a term, literal, etc.
pub trait Values {
    fn values(self) -> ValueSet;
}

impl Values for ValueSet {
    fn values(self) -> ValueSet {
        self
    }
}

impl Values for Pool<GroundTerm> {
    fn values(self) -> ValueSet {
        use Pool::*;
        match self {
            Interval(i, j) => {
                let i = i.values();
                let j = j.values();
                (i..=j).values()
            }
            Set(s) => {
                let mut values = ValueSet::new();
                for x in s {
                    values.extend(x.values());
                }
                values
            }
        }
    }
}

impl Values for GroundTerm {
    fn values(self) -> ValueSet {
        use GroundTerm::*;
        match self {
            Constant(c) => [c].into_iter().collect(),
            Choice(p) => p.values(),
            UnaryOperation(op, x) => {
                use UnaryOp::*;
                let x = x.values();
                match op {
                    Abs => x.abs(),
                    Neg => x.neg(),
                    Not => x.not(),
                }
            }
            BinaryOperation(x, op, y) => {
                use BinOp::*;
                let x = x.values();
                let y = y.values();
                match op {
                    Add => x + y,
                    Sub => x - y,
                    Mul => x * y,
                    Exp => x.pow(y),
                    Div => x / y,
                    Rem => x % y,
                }
            }
        }
    }
}

/// Combine the values of the elements of a vector in all possible ways.
/// See "ASP" Table 4.4.
pub fn all_values<T: Values>(v: Vec<T>) -> Vec<Vec<Constant>> {
    let n = v.len();
    let images = v
        .into_iter()
        .map(|x| x.values().into_iter().collect::<Vec<Constant>>())
        .collect::<Vec<Vec<Constant>>>();
    let radixes = images.iter().map(Vec::len).collect::<Vec<usize>>();
    let mut combinations = Vec::new();
    combinations_mixed(n, &radixes, |a: &[usize]| {
        assert_eq!(a.len(), n);
        combinations.push(
            images
                .iter()
                .zip(a.iter())
                .map(|(image, &i)| image[i].clone())
                .collect::<Vec<Constant>>(),
        );
    });
    combinations
}

/// Apply a binary operation to all combinations of the left and right
/// hand sides' values. The closure takes an accumulator, a left value,
/// and a right value.
pub fn for_all_value_pairs(
    lhs: impl Values,
    rhs: impl Values,
    mut f: impl FnMut(&mut ValueSet, Constant, Constant),
) -> ValueSet {
    let l = lhs.values().into_iter().collect::<Vec<Constant>>();
    let r = rhs.values().into_iter().collect::<Vec<Constant>>();
    let mut v = ValueSet::new();
    combinations_mixed(2, &[l.len(), r.len()], |a: &[usize]| {
        assert_eq!(a.len(), 2);
        let x = l[a[0]].clone();
        let y = r[a[1]].clone();
        f(&mut v, x, y);
    });
    v
}

/// Some arithmetic operations are represented by direct methods instead of
/// `std::ops` traits.
impl ValueSet {
    fn abs(self) -> Self {
        ValueSet::from_iter(self.values().into_iter().filter_map(|x| x.abs()))
    }

    fn neg(self) -> Self {
        ValueSet::from_iter(self.values().into_iter().filter_map(|x| x.neg()))
    }

    fn not(self) -> Self {
        ValueSet::from_iter(self.values().into_iter().filter_map(|x| x.not()))
    }

    fn pow(self, other: Self) -> Self {
        for_all_value_pairs(self, other, |values, x, y| {
            if let Some(z) = x.pow(y) {
                values.insert(z);
            }
        })
    }
}

/// Comparisons on sets of values hold only if they hold for all
/// elements of the set.
impl PartialOrd for ValueSet {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let mut ordering = BTreeSet::<Ordering>::new();
        for_all_value_pairs(self.clone(), other.clone(), |_values, x, y| {
            if let Some(o) = x.partial_cmp(&y) {
                ordering.insert(o);
            }
        });
        if ordering.len() == 1 {
            Some(ordering.into_iter().next().unwrap())
        } else {
            None
        }
    }
}

/// We'll use the Rust range data structures to implement our intervals.
impl Values for ops::RangeInclusive<ValueSet> {
    fn values(self) -> ValueSet {
        for_all_value_pairs(
            self.start().clone(),
            self.end().clone(),
            |values, start, end| {
                use Constant::*;
                if let (Number(start), Number(end)) = (start, end) {
                    values.extend((start..=end).map(Into::into));
                }
            },
        )
    }
}

/// The operators {`+`, `-`, `*`, `/`, `%`} all have standard Rust traits.
/// We implement them for sets of values by applying the operation to all
/// possible left and right hand sides' values.
macro_rules! impl_op_for_values {
    ($trait:path, $method:ident, $binop:path) => {
        impl $trait for ValueSet {
            type Output = Self;

            fn $method(self, rhs: Self) -> Self::Output {
                for_all_value_pairs(self, rhs, |values, x, y| {
                    if let Some(z) = $binop.eval(x, y) {
                        values.insert(z);
                    }
                })
            }
        }
    };
}

impl_op_for_values!(ops::Add, add, BinOp::Add);
impl_op_for_values!(ops::Sub, sub, BinOp::Sub);
impl_op_for_values!(ops::Mul, mul, BinOp::Mul);
impl_op_for_values!(ops::Div, div, BinOp::Div);
impl_op_for_values!(ops::Rem, rem, BinOp::Rem);

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! values {
        [$($val:tt),*] => {
            ValueSet::from_iter([$(constant![$val]),*])
        };
    }

    macro_rules! assert_values {
        ($term:expr, $values:expr) => {
            assert_eq!($term.ground().values(), $values);
        };
    }

    macro_rules! assert_values_eq {
        ($term:expr, $other:expr) => {
            assert_eq!($term.ground().values(), $other.ground().values());
        };
    }

    #[test]
    fn add() {
        assert_values!(term![0 + 0], values![0]);
        assert_values!(term![0 + 1], values![1]);
        assert_values!(term![1 + 2], values![3]);
        assert_values!(term![1 + (2..8)], values![3, 4, 5, 6, 7, 8, 9]);
        assert_values!(term![(1 + (2 + 1000000))], values![1000003]);
        assert_values!(term![1 + foo], values![]);
        assert_values!(term![foo + 1], values![]);
        assert_values!(term![foo + bar], values![foobar]);
    }

    #[test]
    fn sub() {
        assert_values!(term![3 - 2], values![1]);
        assert_values!(term![3 - 3], values![0]);
        assert_values_eq!(term![3 - 5], term![-2]);
        assert_values!(term![foobar - bar], values![foo]);
        assert_values!(term![foobar - quux], values![]);
    }

    #[test]
    fn mul() {
        assert_values!(term![0 * 0], values![0]);
        assert_values!(term![0 * 1], values![0]);
        assert_values!(term![1 * 1], values![1]);
        assert_values!(term![2 * 2], values![4]);
        assert_values!(term![2 * 3], values![6]);
        assert_values!(term![3 * 2], values![6]);
        assert_values!(term![3 * foo], values![foofoofoo]);
        assert_values!(term![foo * 3], values![foofoofoo]);
        assert_values!(term![foo * foo], values![]);
    }

    #[test]
    fn exp() {
        assert_values!(term![2 ^ 3], values![8]);
        assert_values!(term![3 ^ 2], values![9]);
        assert_values!(term![2 ^ (3..5)], values![8, 16, 32]);
        assert_values!(term![(3..5) ^ 2], values![9, 16, 25]);
        assert_values!(
            term![(3..5) ^ (6..10)],
            values![
                729, 2187, 6561, 19683, 59049, 4096, 16384, 65536, 262144, 1048576, 15625, 78125,
                390625, 1953125, 9765625
            ]
        );
    }

    #[test]
    fn div() {
        assert_values!(term![0 / 0], values![]);
        assert_values!(term![1 / 0], values![]);
        assert_values!(term![0 / 1], values![0]);
        assert_values!(term![1 / 2], values![0]);
        assert_values!(term![3 / 2], values![1]);
        assert_values!(term![6 / 3], values![2]);
        assert_values!(term![(-6) / (-3)], values![2]);
        assert_values!(term![((1..3) * 2) / 2], values![1, 2, 3]);
    }

    #[test]
    fn rem() {
        assert_values!(term![0 % 1], values![0]);
        assert_values!(term![1 % 0], values![]);
        assert_values!(term![3 % 2], values![1]);
        assert_values!(term![6 % 3], values![0]);
        assert_values!(term![(-6) % 3], values![0]);
        assert_values!(term![((1..3) * 2) % 2], values![0, 0, 0]);
    }

    #[test]
    fn int() {
        assert_values!(term![1..0], values![]);
        assert_values!(term![0..0], values![0]);
        assert_values!(term![1..3], values![1, 2, 3]);
        assert_values_eq!(term![(1..3) - 1], term![0..2]);
        assert_values_eq!(term![1 - (1..3)], term![(-2)..0]);
        assert_values!(term![(1..3) * 2], values![2, 4, 6]);
        assert_values!(term![(1..3) * (4..5)], values![4, 5, 8, 10, 12, 15]);
        assert_values!(term![(2..4) * (2..4)], values![4, 6, 8, 9, 12, 16]);
        assert_values_eq!(term![(1..3000) * 4000000], term![4000000 * (1..3000)]);
        assert_values!(term![((1..3) - (1..3))], values![(-2), (-1), 0, 1, 2]);
    }

    #[test]
    fn set() {
        assert_values!(term![1], values![1]);
        assert_values!(term![1 or 2 or 3], values![1, 2, 3]);
        assert_values_eq!(term![3 or 2 or 1], term![1 or 2 or 3]);
        assert_values_eq!(term![1 or (2..3)], term![1 or 2 or 3]);
        assert_values_eq!(term![(1..3) or 3], term![1 or 2 or 3]);
        assert_values_eq!(term![(1..3) * 10], term![10 or 20 or 30]);
    }

    #[test]
    fn abs() {
        assert_values!(term![|0|], values![0]);
        assert_values!(term![|1|], values![1]);
        assert_values!(term![|(-1)|], values![1]);
        assert_values_eq!(term![|((-10)..(-5))|], term![5..10]);
    }

    #[test]
    fn neg() {
        assert_values!(term![-0], values![0]);
        assert_values_eq!(term![-1], term![0 - 1]);
        assert_values_eq!(term![-(1 + 1)], term![-2]);
        assert_values_eq!(term![-(1..5)], term![((-5)..(-1))]);
    }

    #[test]
    #[ignore = "no classical negation yet"]
    fn not() {
        todo!()
    }
}
