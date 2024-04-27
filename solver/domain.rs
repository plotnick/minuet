//! Finite domains as sparse sets with reversible memory
//! (Knuth §7.2.2.3, Christmas Lecture 2023). They are
//! intended as auxiliary data structures in backtracking
//! search through large (combinatorial) spaces.

use std::cmp::Ord;
use std::collections::BTreeMap;
use std::fmt;

/// A finite domain `D` with reversible element deletion.
pub trait Domain<T> {
    /// Is `x ∈ D`?
    #[allow(dead_code)]
    fn contains(&self, x: &T) -> bool;

    /// If `x ∈ D`, delete it and return `true`, otherwise return `false`.
    fn delete(&mut self, x: &T) -> bool;

    /// Return a slice of deleted elements up to size `n`.
    fn deleted(&self, n: usize) -> &[T];

    /// Get a reference to the first item.
    #[allow(dead_code)]
    fn first(&self) -> Option<&T> {
        self.get(0)
    }

    /// Get a reference to a current value by index.
    fn get(&self, i: usize) -> Option<&T>;

    /// Undelete elements to restore the domain to size `n`.
    /// Return `true` if the restoration was successful (i.e.,
    /// if the original domain had `n` or more elements).
    fn restore(&mut self, n: usize) -> bool;

    /// Determine the current size |`D`|.
    fn len(&self) -> usize;

    /// Return `true` if the domain currently has no elements.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Iterate over the current elements of `D`.
    fn iter(&self) -> DomainIterator<T>;
}

/// An iterator over the current elements of a domain `D`.
pub struct DomainIterator<'a, T> {
    domain: &'a dyn Domain<T>,
    index: usize,
}

impl<'a, T> DomainIterator<'a, T> {
    pub fn new(domain: &'a dyn Domain<T>) -> Self {
        Self { domain, index: 0 }
    }
}

impl<'a, T> Iterator for DomainIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let i = self.index;
        if i < self.domain.len() {
            self.index += 1;
            self.domain.get(i)
        } else {
            None
        }
    }
}

/// A sparse set of integers in the range `0..len`.
pub struct SparseIntegerSet<T: Copy + Ord> {
    /// A permutation of the elements.
    dom: Vec<T>,

    /// The inverse permutation of `dom`.
    /// Knuth calls this `IDOM`.
    map: BTreeMap<T, usize>,

    /// How many elements are currently present.
    len: usize,
}

impl<T: Copy + Ord> SparseIntegerSet<T> {
    pub fn new(elements: impl IntoIterator<Item = T>) -> Self {
        let dom = elements.into_iter().collect::<Vec<T>>();
        let len = dom.len();
        let map = dom
            .iter()
            .copied()
            .enumerate()
            .map(|(i, x)| (x, i))
            .collect::<BTreeMap<T, usize>>();
        Self { dom, map, len }
    }

    fn check_invariants(&self) {
        assert!(self.len <= self.dom.len(), "invalid domain length");
        assert_eq!(self.dom.len(), self.map.len(), "invalid map length");
    }

    // TODO: move to the trait, if possible
    pub fn delete_if(&mut self, mut f: impl FnMut(&T) -> bool) -> &[T] {
        let n = self.len;
        for i in (0..self.len).rev() {
            let x = self.dom[i]; // copy
            if f(&x) {
                self.delete(&x);
            }
        }
        self.deleted(n)
    }

    pub fn first(&self) -> Option<T> {
        self.dom.first().copied()
    }
}

impl<T: Copy + Ord + fmt::Debug> fmt::Debug for SparseIntegerSet<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.dom[0..self.len].iter()).finish()
    }
}

impl<T: Copy + Ord> FromIterator<T> for SparseIntegerSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self::new(iter)
    }
}

impl<T: Copy + Ord> Domain<T> for SparseIntegerSet<T> {
    fn contains(&self, x: &T) -> bool {
        self.map.get(x).map(|&i| i < self.len).unwrap_or(false)
    }

    fn delete(&mut self, x: &T) -> bool {
        self.check_invariants();
        let i = self.map.get(x).copied().unwrap_or(self.len);
        if i < self.len {
            self.len -= 1;
            let j = self.len;
            self.dom.swap(i, j);
            let y = &self.dom[i];
            *(self.map.get_mut(x).expect("missing map entry for x")) = j;
            *(self.map.get_mut(y).expect("missing map entry for y")) = i;
            true
        } else {
            false
        }
    }

    fn deleted(&self, n: usize) -> &[T] {
        &self.dom[self.len..n]
    }

    fn get(&self, i: usize) -> Option<&T> {
        self.dom.get(i)
    }

    fn restore(&mut self, n: usize) -> bool {
        self.check_invariants();
        if n <= self.dom.len() {
            self.len = n;
            true
        } else {
            false
        }
    }

    fn len(&self) -> usize {
        self.len
    }

    fn iter(&self) -> DomainIterator<T> {
        DomainIterator::new(self)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn sparse_integer_set() {
        let mut dom = SparseIntegerSet::new(0..7);
        assert!(!dom.contains(&7));
        assert_eq!(
            dom.iter().copied().collect::<Vec<_>>(),
            vec![0, 1, 2, 3, 4, 5, 6]
        );
        assert_eq!(dom.first(), Some(0));
        assert!(dom.contains(&0));
        assert!(dom.delete(&0));
        assert!(!dom.contains(&0));
        assert!(dom.delete(&2));
        assert!(dom.delete(&6));
        assert!(!dom.delete(&7));
        assert_eq!(dom.len(), 4);
        assert_eq!(dom.iter().copied().collect::<Vec<_>>(), vec![4, 1, 5, 3]);
        assert!(dom.restore(7));
        assert!(!dom.restore(8));
        assert_eq!(
            dom.iter().copied().collect::<Vec<_>>(),
            vec![4, 1, 5, 3, 6, 2, 0]
        );
    }

    #[test]
    fn deleted() {
        let mut dom = SparseIntegerSet::new(0..3);
        assert_eq!(dom.iter().copied().collect::<Vec<_>>(), vec![0, 1, 2]);
        assert!(dom.delete(&0));
        assert!(dom.delete(&1));
        assert_eq!(dom.deleted(3), [1, 0]);
        assert_eq!(dom.iter().copied().collect::<Vec<_>>(), vec![2]);
    }
}
