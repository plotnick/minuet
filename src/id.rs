//! A [newtype](https://rust-unofficial.github.io/patterns/patterns/behavioural/newtype.html)
//! wrapper around unsigned integers used as IDs for arbitrary objects.
//! The prevents us from confusing, say, an item ID with an option ID,
//! even though they're both represented by a `usize`.

use std::marker::PhantomData;
use std::ops::{Index, IndexMut};
use std::slice::Iter;

/// An unsigned integer ID with type-level information about its object.
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct Id<T>(usize, PhantomData<T>);

impl<T> Id<T> {
    pub fn new(id: usize, _object: &T) -> Self {
        Self(id, PhantomData)
    }

    pub fn min() -> Self {
        Self(0, PhantomData)
    }

    pub fn max() -> Self {
        Self(usize::MAX, PhantomData)
    }
}

impl<T> Clone for Id<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Id<T> {}

/// A vector indexed by typed ID.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct IdVec<T, I>(Vec<T>, PhantomData<I>);

impl<T, I> IdVec<T, I> {
    pub fn id(&self, id: usize) -> Id<T> {
        Id::new(id, &self.0[id])
    }

    pub fn into_vec(self) -> Vec<T> {
        self.0
    }

    pub fn iter(&self) -> Iter<'_, T> {
        self.0.iter()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn push(&mut self, value: T) {
        self.0.push(value)
    }
}

impl<T, U> From<Vec<T>> for IdVec<T, U> {
    fn from(value: Vec<T>) -> Self {
        IdVec(value, PhantomData)
    }
}

impl<T, U> FromIterator<T> for IdVec<T, U> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self(iter.into_iter().collect(), PhantomData)
    }
}

impl<T, U> Index<Id<U>> for IdVec<T, U> {
    type Output = T;

    fn index(&self, index: Id<U>) -> &Self::Output {
        self.0.index(index.0)
    }
}

impl<T, U> IndexMut<Id<U>> for IdVec<T, U> {
    fn index_mut(&mut self, index: Id<U>) -> &mut Self::Output {
        self.0.index_mut(index.0)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn id() {
        struct Foo();
        let foo = Foo();
        let id = Id::<Foo>::new(0, &foo);
        assert_eq!(id.0, 0);
    }

    #[test]
    fn id_vec() {
        #[derive(Clone, Debug, Eq, PartialEq)]
        struct Bar(u8);
        let bars = vec![Bar(0), Bar(1), Bar(2)];
        let ids = IdVec::from(bars.clone());
        assert_eq!(ids[Id::new(0, &bars[0])], Bar(0));
        assert_eq!(ids[Id::new(1, &bars[1])], Bar(1));
        assert_eq!(ids[Id::new(2, &bars[2])], Bar(2));
    }
}
