//! Operations on sets of constant values.
//! See "Abstract Gringo" § 4.2 and "ASP" §§ 4.6-7.

use std::cmp::Ordering;
use std::collections::btree_set::{self, BTreeSet};
use std::fmt;
use std::iter::FromIterator;
use std::ops;

use minuet_syntax::*;

use crate::generate::combinations_mixed;
use crate::ground::*;

/// A *value* is either a constant (name, number) or
/// a *symbolic function* (see "ASP" § 6.6).
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Value {
    Constant(Constant),
    Function(Application<GroundTerm>),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constant(c) => f.write_fmt(format_args!("{c}")),
            Self::Function(a) => f.write_fmt(format_args!("{a}")),
        }
    }
}

/// A set of values denoted by some term.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValueSet(BTreeSet<Value>);

impl ValueSet {
    pub fn new() -> Self {
        Self(BTreeSet::new())
    }

    pub fn contains(&self, v: &Value) -> bool {
        self.0.contains(v)
    }

    pub fn insert(&mut self, v: Value) {
        self.0.insert(v);
    }
}

impl Default for ValueSet {
    fn default() -> Self {
        Self::new()
    }
}

impl Extend<Value> for ValueSet {
    fn extend<Iter: IntoIterator<Item = Value>>(&mut self, iter: Iter) {
        iter.into_iter().for_each(move |elem| {
            self.insert(elem);
        });
    }
}

impl FromIterator<Value> for ValueSet {
    fn from_iter<I: IntoIterator<Item = Value>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl IntoIterator for ValueSet {
    type Item = Value;
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
            Constant(v) => ValueSet::from_iter([*v]),
            Pool(p) => p.values(),
            UnaryOperation(op, x) => {
                use UnaryOp::*;
                let x = x.values();
                match op {
                    Abs => x.abs(),
                    Neg => -x,
                    Not => !x,
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
pub fn all_values<T: Values>(v: Vec<T>) -> Vec<Vec<Value>> {
    let n = v.len();
    let images = v
        .into_iter()
        .map(|x| x.values().into_iter().collect::<Vec<Value>>())
        .collect::<Vec<Vec<Value>>>();
    let radixes = images.iter().map(Vec::len).collect::<Vec<usize>>();
    let mut combinations = Vec::new();
    combinations_mixed(n, &radixes, |a: &[usize]| {
        assert_eq!(a.len(), n);
        combinations.push(
            images
                .iter()
                .zip(a.iter())
                .flat_map(|(image, &i)| image.get(i).cloned())
                .collect::<Vec<Value>>(),
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
    mut f: impl FnMut(&mut ValueSet, Value, Value),
) -> ValueSet {
    let l = lhs.values().into_iter().collect::<Vec<Value>>();
    let r = rhs.values().into_iter().collect::<Vec<Value>>();
    let mut v = ValueSet::new();
    combinations_mixed(2, &[l.len(), r.len()], |a: &[usize]| {
        assert_eq!(a.len(), 2);
        let x = l[a[0]].clone();
        let y = r[a[1]].clone();
        f(&mut v, x, y);
    });
    v
}

/// Arithmetic operations represented by direct methods
/// instead of `std::ops` traits.
impl ValueSet {
    fn abs(self) -> Self {
        ValueSet::from_iter(self.values().into_iter().filter_map(|x| match x {
            Value::Constant(c) => c.abs().map(Value::Constant),
            Value::Function(_) => None,
        }))
    }

    fn pow(self, other: Self) -> Self {
        for_all_value_pairs(self, other, |values, x, y| {
            if let (Value::Constant(x), Value::Constant(y)) = (x, y) {
                if let Some(z) = x.pow(y) {
                    values.insert(Value::Constant(z));
                }
            }
        })
    }
}

/// Comparisons on sets of values hold only if and only if
/// they hold for all elements of the set.
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
                if let (
                    Value::Constant(Constant::Number(start)),
                    Value::Constant(Constant::Number(end)),
                ) = (start, end)
                {
                    values.extend((start..=end).map(Constant::Number).map(Value::Constant));
                }
            },
        )
    }
}

/// The binary operators {`+`, `-`, `*`, `/`, `%`} all have standard Rust
/// traits. We implement them for sets of values by applying the operation
/// to all possible left and right hand sides' values.
macro_rules! impl_bin_op_for_values {
    ($trait:path, $method:ident, $binop:path) => {
        impl $trait for ValueSet {
            type Output = Self;

            fn $method(self, rhs: Self) -> Self::Output {
                for_all_value_pairs(self, rhs, |values, x, y| {
                    if let (Value::Constant(x), Value::Constant(y)) = (x, y) {
                        if let Some(z) = $binop.eval(x, y) {
                            values.insert(Value::Constant(z));
                        }
                    }
                })
            }
        }
    };
}

impl_bin_op_for_values!(ops::Add, add, BinOp::Add);
impl_bin_op_for_values!(ops::Sub, sub, BinOp::Sub);
impl_bin_op_for_values!(ops::Mul, mul, BinOp::Mul);
impl_bin_op_for_values!(ops::Div, div, BinOp::Div);
impl_bin_op_for_values!(ops::Rem, rem, BinOp::Rem);

/// Unary numerical negation.
impl ops::Neg for ValueSet {
    type Output = Self;

    fn neg(self) -> Self::Output {
        ValueSet::from_iter(self.values().into_iter().filter_map(|x| match x {
            Value::Constant(x) => (-x).map(Value::Constant),
            _ => None,
        }))
    }
}

/// Unary logical negation.
impl ops::Not for ValueSet {
    type Output = Self;

    fn not(self) -> Self {
        ValueSet::from_iter(self.values().into_iter().filter_map(|x| match x {
            Value::Constant(x) => (!x).map(Value::Constant),
            _ => None,
        }))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! values {
        [$($val: literal),*] => {
            ValueSet::from_iter([$(Value::Constant(Constant::from($val))),*])
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
        assert_values!(binary!(0, Add, 0), values!(0));
        assert_values!(binary!(0, Add, 1), values!(1));
        assert_values!(binary!(1, Add, 2), values!(3));
        assert_values!(binary!(1, Add, pool!(2..8)), values!(3, 4, 5, 6, 7, 8, 9));
        assert_values!(binary!(1, Add, binary!(2, Add, 1000000)), values!(1000003));
        assert_values!(binary!(1, Add, "foo"), values!());
        assert_values!(binary!("foo", Add, 1), values!());
        assert_values!(binary!("foo", Add, "bar"), values!("foobar"));
    }

    #[test]
    fn sub() {
        assert_values!(binary!(3, Sub, 2), values!(1));
        assert_values!(binary!(3, Sub, 3), values!(0));
        assert_values_eq!(binary!(3, Sub, 5), constant!(-2));
        assert_values!(binary!("foobar", Sub, "bar"), values!("foo"));
        assert_values!(binary!("foobar", Sub, "quux"), values!());
    }

    #[test]
    fn mul() {
        assert_values!(binary!(0, Mul, 0), values!(0));
        assert_values!(binary!(0, Mul, 1), values!(0));
        assert_values!(binary!(1, Mul, 1), values!(1));
        assert_values!(binary!(2, Mul, 2), values!(4));
        assert_values!(binary!(2, Mul, 3), values!(6));
        assert_values!(binary!(3, Mul, 2), values!(6));
        assert_values!(binary!(3, Mul, "foo"), values!("foofoofoo"));
        assert_values!(binary!("foo", Mul, 3), values!("foofoofoo"));
        assert_values!(binary!("foo", Mul, "foo"), values!());
    }

    #[test]
    fn exp() {
        assert_values!(binary!(2, Exp, 3), values!(8));
        assert_values!(binary!(3, Exp, 2), values!(9));
        assert_values!(binary!(2, Exp, pool!(3..5)), values!(8, 16, 32));
        assert_values!(binary!(pool!(3..5), Exp, 2), values!(9, 16, 25));
        assert_values!(
            binary!(pool!(3..5), Exp, pool!(6..10)),
            values!(
                729, 2187, 6561, 19683, 59049, 4096, 16384, 65536, 262144, 1048576, 15625, 78125,
                390625, 1953125, 9765625
            )
        );
    }

    #[test]
    fn div() {
        assert_values!(binary!(0, Div, 0), values!());
        assert_values!(binary!(1, Div, 0), values!());
        assert_values!(binary!(0, Div, 1), values!(0));
        assert_values!(binary!(1, Div, 2), values!(0));
        assert_values!(binary!(3, Div, 2), values!(1));
        assert_values!(binary!(6, Div, 3), values!(2));
        assert_values!(binary!(-6, Div, -3), values!(2));
        assert_values!(
            binary!(binary!(pool!(1..3), Mul, 2), Div, 2),
            values!(1, 2, 3)
        );
    }

    #[test]
    fn rem() {
        assert_values!(binary!(0, Rem, 1), values!(0));
        assert_values!(binary!(1, Rem, 0), values!());
        assert_values!(binary!(3, Rem, 2), values!(1));
        assert_values!(binary!(6, Rem, 3), values!(0));
        assert_values!(binary!(-6, Rem, 3), values!(0));
        assert_values!(
            binary!(binary!(pool!(1..3), Mul, 2), Rem, 2),
            values!(0, 0, 0)
        );
    }

    #[test]
    fn int() {
        assert_values!(pool!(1..0), values!());
        assert_values!(pool!(0..0), values!(0));
        assert_values!(pool!(1..3), values!(1, 2, 3));
        assert_values_eq!(binary!(pool!(1..3), Sub, 1), pool!(0..2));
        assert_values_eq!(binary!(1, Sub, pool!(1..3)), pool!(-2..0));
        assert_values!(binary!(pool!(1..3), Mul, 2), values!(2, 4, 6));
        assert_values!(
            binary!(pool!(1..3), Mul, pool!(4..5)),
            values!(4, 5, 8, 10, 12, 15)
        );
        assert_values!(
            binary!(pool!(2..4), Mul, pool!(2..4)),
            values!(4, 6, 8, 9, 12, 16)
        );
        assert_values_eq!(
            binary!(pool!(1..3000), Mul, 4000000),
            binary!(4000000, Mul, pool!(1..3000))
        );
        assert_values!(
            binary!(pool!(1..3), Sub, pool!(1..3)),
            values!(-2, -1, 0, 1, 2)
        );
    }

    #[test]
    fn set() {
        assert_values!(pool!({ 1 }), values!(1));
        assert_values!(pool!({1, 2, 3}), values!(1, 2, 3));
        assert_values_eq!(pool!({3, 2, 1}), pool!({1, 2, 3}));
        assert_values_eq!(pool!({1, pool!(2..3)}), pool!({1, 2, 3}));
        assert_values_eq!(pool!({pool!(1..3), 3}), pool!({1, 2, 3}));
        assert_values_eq!(binary!(pool!(1..3), Mul, 10), pool!({10, 20, 30}));
    }

    #[test]
    fn abs() {
        assert_values!(unary!(Abs, 0), values!(0));
        assert_values!(unary!(Abs, 1), values!(1));
        assert_values!(unary!(Abs, -1), values!(1));
        assert_values_eq!(unary!(Abs, pool!(-10..-5)), pool!(5..10));
    }

    #[test]
    fn neg() {
        assert_values!(unary!(Neg, 0), values!(0));
        assert_values_eq!(unary!(Neg, 1), binary!(0, Sub, 1));
        assert_values_eq!(unary!(Neg, binary!(1, Add, 1)), constant!(-2));
        assert_values_eq!(unary!(Neg, pool!(1..5)), pool!(-5..-1));
    }

    #[test]
    #[ignore = "no classical negation yet"]
    fn not() {
        todo!()
    }

    #[test]
    fn cmp() {
        assert!(pool!(-2..0).ground().values() < pool!(1..3).ground().values());
        assert!(pool!(1..3).ground().values() > pool!(-2..0).ground().values());
        assert!(pool!(1..3).ground().values() >= pool!(-2..0).ground().values());
        assert!(pool!(-2..1)
            .ground()
            .values()
            .partial_cmp(&pool!(1..3).ground().values())
            .is_none());
        assert!(pool!(-2..1)
            .ground()
            .values()
            .partial_cmp(&pool!(1..3).ground().values())
            .is_none());
    }
}
