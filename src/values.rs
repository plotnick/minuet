//! Representations and operations on sets of constant values.
//! See "Abstract Gringo" §4.2 and Lifschitz, "ASP" §4.6.
//!
//! We allow arithmetic operations to mix numbers and symbols (as strings);
//! this may be a mistake. But all such methods return `Option<Constant>`,
//! so we don't need to define all possible operations.

use std::cmp::Ordering;
use std::collections::btree_set::{self, BTreeSet};
use std::iter::FromIterator;
use std::ops;

use crate::generate::combinations_mixed;
use crate::syntax::*;

/// A set of constants denoted by some term.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Values(BTreeSet<Constant>);

impl Values {
    fn new() -> Self {
        Self(BTreeSet::new())
    }

    fn insert(&mut self, c: Constant) {
        self.0.insert(c);
    }
}

impl Extend<Constant> for Values {
    fn extend<Iter: IntoIterator<Item = Constant>>(&mut self, iter: Iter) {
        iter.into_iter().for_each(move |elem| {
            self.insert(elem);
        });
    }
}

impl FromIterator<Constant> for Values {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Constant>,
    {
        Self(iter.into_iter().collect())
    }
}

impl IntoIterator for Values {
    type Item = Constant;
    type IntoIter = btree_set::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

/// Anything that denotes a set of constants, e.g., intervals `I..J`,
/// choices `{p(X)}` and `p(X or Y)`, etc.
pub trait Image {
    fn image(&self) -> Values;
}

impl Image for Constant {
    fn image(&self) -> Values {
        Values::from_iter([self.clone()])
    }
}

impl Image for Pool<GroundTerm> {
    fn image(&self) -> Values {
        use Pool::*;
        match self {
            Interval(i, j) => {
                let i = i.image();
                let j = j.image();
                (i..=j).image()
            }
            Set(s) => {
                let mut values = Values::new();
                for x in s {
                    values.extend(x.image());
                }
                values
            }
        }
    }
}

impl Image for Values {
    fn image(&self) -> Values {
        self.clone()
    }
}

impl Image for GroundTerm {
    fn image(&self) -> Values {
        use GroundTerm::*;
        match self {
            Constant(c) => [c].into_iter().cloned().collect(),
            Choice(p) => p.image(),
            UnaryOperation(op, x) => {
                use UnaryOp::*;
                let x = x.image();
                match op {
                    Abs => x.abs(),
                    Neg => x.neg(),
                    Not => x.not(),
                }
            }
            BinaryOperation(x, op, y) => {
                use BinOp::*;
                let x = x.image();
                let y = y.image();
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

pub trait IntoImage {
    fn into_image(self) -> Vec<Self>
    where
        Self: Sized;
}

impl IntoImage for GroundTerm {
    fn into_image(self) -> Vec<Self> {
        self.image().into_iter().map(Self::Constant).collect()
    }
}

impl IntoImage for Atom<GroundTerm> {
    fn into_image(self) -> Vec<Self> {
        let Atom {
            predicate,
            arguments,
        } = self;
        arguments
            .into_image()
            .into_iter()
            .map(|args| Atom::new(predicate.clone(), args))
            .collect()
    }
}

impl IntoImage for Literal<GroundTerm> {
    /// Expand intervals & choices in a literal.
    fn into_image(self) -> Vec<Self> {
        use Literal::*;
        match self {
            Positive(atom) => atom.into_image().into_iter().map(Positive).collect(),
            Negative(atom) => atom.into_image().into_iter().map(Negative).collect(),
            DoubleNegative(atom) => atom.into_image().into_iter().map(DoubleNegative).collect(),
            Relation(x, op, y) => vec![*x, *y]
                .into_image()
                .into_iter()
                .map(|mut v| {
                    let y = v.pop().expect("missing arg");
                    let x = v.pop().expect("missing arg");
                    assert!(v.is_empty(), "non-binary relation");
                    Literal::relation(x, op, y)
                })
                .collect(),
        }
    }
}

impl<T> IntoImage for Vec<T>
where
    T: Clone + IntoImage,
{
    /// Combine the images of the elements of a vector in all possible ways.
    fn into_image(self) -> Vec<Self> {
        let n = self.len();
        let images = self
            .into_iter()
            .map(IntoImage::into_image)
            .collect::<Vec<Vec<T>>>();
        let radixes = images.iter().map(Vec::len).collect::<Vec<usize>>();
        let mut combinations = Vec::<Vec<T>>::new();
        combinations_mixed(n, &radixes, |a: &[usize]| {
            assert_eq!(a.len(), n);
            combinations.push(
                images
                    .iter()
                    .zip(a.iter())
                    .map(|(image, &i)| image[i].clone())
                    .collect::<Vec<T>>(),
            );
        });
        combinations
    }
}

/// Apply a binary operation to all combinations of the left
/// and right hand sides' values. The closure takes an accumulator,
/// a left, and a right value.
fn for_all_values(
    lhs: &impl Image,
    rhs: &impl Image,
    mut f: impl FnMut(&mut Values, Constant, Constant),
) -> Values {
    let l = lhs.image().into_iter().collect::<Vec<Constant>>();
    let r = rhs.image().into_iter().collect::<Vec<Constant>>();
    let mut v = Values::new();
    combinations_mixed(2, &[l.len(), r.len()], |a: &[usize]| {
        assert_eq!(a.len(), 2);
        let x = l[a[0]].clone();
        let y = r[a[1]].clone();
        f(&mut v, x, y);
    });
    v
}

/// Some operations are represented by direct methods instead of `ops` traits.
impl Values {
    fn abs(self) -> Self {
        Values::from_iter(self.image().into_iter().filter_map(|x| x.abs()))
    }

    fn neg(self) -> Self {
        Values::from_iter(self.image().into_iter().filter_map(|x| x.neg()))
    }

    fn not(self) -> Self {
        Values::from_iter(self.image().into_iter().filter_map(|x| x.not()))
    }

    fn pow(self, other: Self) -> Self {
        for_all_values(&self, &other, |values, x, y| {
            if let Some(z) = x.pow(y) {
                values.insert(z);
            }
        })
    }
}

/// Comparisons.
impl PartialOrd for Values {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let mut ordering = BTreeSet::<Ordering>::new();
        for_all_values(self, other, |_values, x, y| {
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

/// Ranges have some traits, but we'll just use the data structure raw
/// to implement our intervals.
impl Image for ops::RangeInclusive<Values> {
    fn image(&self) -> Values {
        for_all_values(self.start(), self.end(), |values, start, end| {
            use Constant::*;
            if let (Number(start), Number(end)) = (start, end) {
                values.extend((start..=end).map(Into::into));
            }
        })
    }
}

/// The operators {`+`, `-`, `*`, `/`, `%`} all have standard Rust traits.
/// Implement them by applying the operation to all possible left and right
/// hand sides' values.
macro_rules! impl_op_for_values {
    ($trait:path, $method:ident, $binop:path) => {
        impl $trait for Values {
            type Output = Self;

            fn $method(self, rhs: Self) -> Self::Output {
                for_all_values(&self, &rhs, |values, x, y| {
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

impl ops::Add for Constant {
    type Output = Option<Self>;

    fn add(self, rhs: Self) -> Self::Output {
        use Constant::*;
        match (self, rhs) {
            (Name(_), Number(_)) | (Number(_), Name(_)) => None,
            (Number(x), Number(y)) => Some(Number(x + y)),
            (Name(a), Name(b)) => Some(Name(Symbol::new({
                let mut x = a.name().to_owned();
                x.push_str(b.name());
                x
            }))),
        }
    }
}

impl ops::Sub for Constant {
    type Output = Option<Self>;

    fn sub(self, rhs: Self) -> Self::Output {
        use Constant::*;
        match (self, rhs) {
            (Name(_), Number(_)) | (Number(_), Name(_)) => None,
            (Number(x), Number(y)) => Some(Number(x - y)),
            (Name(a), Name(b)) => a
                .name()
                .strip_suffix(b.name())
                .map(|diff| Name(Symbol::new(String::from(diff)))),
        }
    }
}

impl ops::Mul for Constant {
    type Output = Option<Self>;

    fn mul(self, rhs: Self) -> Self::Output {
        use Constant::*;
        match (self, rhs) {
            (Name(_), Name(_)) => None,
            (Number(x), Number(y)) => Some(Number(x * y)),
            (Name(a), Number(n)) | (Number(n), Name(a)) => Some(Name(Symbol::new({
                let mut x = String::new();
                for _ in 0..n {
                    x.push_str(a.name());
                }
                x
            }))),
        }
    }
}

impl ops::Div for Constant {
    type Output = Option<Self>;

    fn div(self, rhs: Self) -> Self::Output {
        use Constant::*;
        match (self, rhs) {
            (Number(_) | Name(_), Name(_)) => None,
            (Number(_), Number(0)) => None,
            (Number(x), Number(y)) => Some(Number(x / y)),
            (Name(name), Number(number)) => todo!("{name} / {number}"),
        }
    }
}

impl ops::Rem for Constant {
    type Output = Option<Self>;

    fn rem(self, rhs: Self) -> Self::Output {
        use Constant::*;
        match (self, rhs) {
            (Number(_) | Name(_), Name(_)) => None,
            (Number(_), Number(0)) => None,
            (Number(x), Number(y)) => Some(Number(x % y)),
            (Name(name), Number(number)) => todo!("{name} % {number}"),
        }
    }
}

impl Constant {
    fn abs(self) -> Option<Self> {
        use Constant::*;
        if let Number(x) = self {
            Some(Number(x.abs()))
        } else {
            None
        }
    }

    fn neg(self) -> Option<Self> {
        use Constant::*;
        if let Number(x) = self {
            Some(Number(-x))
        } else {
            None
        }
    }

    fn not(self) -> Option<Self> {
        todo!("classical negation")
    }

    pub fn pow(self, rhs: Self) -> Option<Self> {
        use Constant::*;
        if let (Number(x), Number(y)) = (self, rhs) {
            if let Ok(y) = u32::try_from(y) {
                return Some(Number(x.pow(y)));
            }
        }
        None
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::formula::Groundable as _;

    macro_rules! ground {
        ($term:expr) => {
            $term.ground_new()
        };
    }

    macro_rules! ground_all {
        ($($term:expr),* $(,)?) => { vec![$(ground!($term)),*] };
    }

    macro_rules! image {
        ($term:expr) => {
            ground!($term).image()
        };
    }
    macro_rules! image_atoms {
        ($term:expr) => {
            ground!($term).into_image()
        };
    }

    macro_rules! values {
        [$($val:tt),*] => {
            Values::from_iter([$(constant![$val]),*])
        };
    }

    macro_rules! assert_image {
        ($term:expr, $image:expr) => {
            assert_eq!(image!($term), $image);
        };
    }

    macro_rules! assert_image_eq {
        ($term:expr, $other:expr) => {
            assert_eq!(image!($term), image!($other));
        };
    }

    #[test]
    fn add() {
        assert_image!(term![0 + 0], values![0]);
        assert_image!(term![0 + 1], values![1]);
        assert_image!(term![1 + 2], values![3]);
        assert_image!(term![1 + (2..8)], values![3, 4, 5, 6, 7, 8, 9]);
        assert_image!(term![(1 + (2 + 1000000))], values![1000003]);
        assert_image!(term![1 + foo], values![]);
        assert_image!(term![foo + 1], values![]);
        assert_image!(term![foo + bar], values![foobar]);
    }

    #[test]
    fn sub() {
        assert_image!(term![3 - 2], values![1]);
        assert_image!(term![3 - 3], values![0]);
        assert_image_eq!(term![3 - 5], term![-2]);
        assert_image!(term![foobar - bar], values![foo]);
        assert_image!(term![foobar - quux], values![]);
    }

    #[test]
    fn mul() {
        assert_image!(term![0 * 0], values![0]);
        assert_image!(term![0 * 1], values![0]);
        assert_image!(term![1 * 1], values![1]);
        assert_image!(term![2 * 2], values![4]);
        assert_image!(term![2 * 3], values![6]);
        assert_image!(term![3 * 2], values![6]);
        assert_image!(term![3 * foo], values![foofoofoo]);
        assert_image!(term![foo * 3], values![foofoofoo]);
        assert_image!(term![foo * foo], values![]);
    }

    #[test]
    fn exp() {
        assert_image!(term![2 ^ 3], values![8]);
        assert_image!(term![3 ^ 2], values![9]);
        assert_image!(term![2 ^ (3..5)], values![8, 16, 32]);
        assert_image!(term![(3..5) ^ 2], values![9, 16, 25]);
        assert_image!(
            term![(3..5) ^ (6..10)],
            values![
                729, 2187, 6561, 19683, 59049, 4096, 16384, 65536, 262144, 1048576, 15625, 78125,
                390625, 1953125, 9765625
            ]
        );
    }

    #[test]
    fn div() {
        assert_image!(term![0 / 1], values![0]);
        assert_image!(term![1 / 0], values![]);
        assert_image!(term![3 / 2], values![1]);
        assert_image!(term![6 / 3], values![2]);
        assert_image!(term![(-6) / (-3)], values![2]);
        assert_image!(term![((1..3) * 2) / 2], values![1, 2, 3]);
    }

    #[test]
    fn rem() {
        assert_image!(term![0 % 1], values![0]);
        assert_image!(term![1 % 0], values![]);
        assert_image!(term![3 % 2], values![1]);
        assert_image!(term![6 % 3], values![0]);
        assert_image!(term![(-6) % 3], values![0]);
        assert_image!(term![((1..3) * 2) % 2], values![0, 0, 0]);
    }

    #[test]
    fn int() {
        assert_image!(term![1..0], values![]);
        assert_image!(term![0..0], values![0]);
        assert_image!(term![1..3], values![1, 2, 3]);
        assert_image_eq!(term![(1..3) - 1], term![0..2]);
        assert_image_eq!(term![1 - (1..3)], term![(-2)..0]);
        assert_image!(term![(1..3) * 2], values![2, 4, 6]);
        assert_image!(term![(1..3) * (4..5)], values![4, 5, 8, 10, 12, 15]);
        assert_image!(term![(2..4) * (2..4)], values![4, 6, 8, 9, 12, 16]);
        assert_image_eq!(term![(1..3000) * 4000000], term![4000000 * (1..3000)]);
    }

    #[test]
    fn set() {
        assert_image!(term![1], values![1]);
        assert_image!(term![1 or 2 or 3], values![1, 2, 3]);
        assert_image_eq!(term![3 or 2 or 1], term![1 or 2 or 3]);
        assert_image_eq!(term![1 or (2..3)], term![1 or 2 or 3]);
        assert_image_eq!(term![(1..3) or 3], term![1 or 2 or 3]);
        assert_image_eq!(term![(1..3) * 10], term![10 or 20 or 30]);
    }

    #[test]
    fn abs() {
        assert_image!(term![|0|], values![0]);
        assert_image!(term![|1|], values![1]);
        assert_image!(term![|(-1)|], values![1]);
        assert_image_eq!(term![|((-10)..(-5))|], term![5..10]);
    }

    #[test]
    fn neg() {
        assert_image!(term![-0], values![0]);
        assert_image_eq!(term![-1], term![0 - 1]);
        assert_image_eq!(term![-(1 + 1)], term![-2]);
        assert_image_eq!(term![-(1..5)], term![((-5)..(-1))]);
    }

    #[test]
    #[ignore = "classical negation"]
    fn not() {
        todo!()
    }

    #[test]
    fn atomic_image() {
        assert_eq!(image_atoms!(atom![p]), ground_all![atom![p]]);
        assert_eq!(image_atoms!(atom![p(1)]), ground_all![atom![p(1)]]);
        assert_eq!(image_atoms!(atom![p(1..1)]), ground_all![atom![p(1)]]);
        assert_eq!(
            image_atoms!(atom![p(1..2)]),
            ground_all![atom![p(1)], atom![p(2)]]
        );
        assert_eq!(image_atoms!(atom![p(1, 2)]), ground_all![atom![p(1, 2)]]);
        assert_eq!(
            image_atoms!(atom![p(1..2, 2..3)]),
            ground_all![
                atom![p(1, 2)],
                atom![p(1, 3)],
                atom![p(2, 2)],
                atom![p(2, 3)]
            ]
        );
        assert_eq!(
            image_atoms!(atom![p(1..2, 2..3, 3..4)]),
            ground_all![
                atom![p(1, 2, 3)],
                atom![p(1, 2, 4)],
                atom![p(1, 3, 3)],
                atom![p(1, 3, 4)],
                atom![p(2, 2, 3)],
                atom![p(2, 2, 4)],
                atom![p(2, 3, 3)],
                atom![p(2, 3, 4)],
            ]
        );
    }
}
