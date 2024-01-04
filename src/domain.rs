//! Finite domains as sparse sets with reversible memory
//! (Knuth §7.2.2.3, Christmas Lecture 2023). They are
//! intended as auxiliary data structures in backtracking
//! search through large (combinatorial) spaces.

#[allow(unused_imports)]
pub use self::hash::SparseHashSet;
pub use self::uint::SparseIntegerSet;

/// A finite domain `D` with reversible element deletion.
pub trait Domain<T> {
    /// Determine whether or not `x∈D`.
    fn contains(&self, x: &T) -> bool;

    /// Delete a given value `x` from `D` and return `true`
    /// if it was present.
    fn delete(&mut self, x: &T) -> bool;

    /// Return a slice of deleted elements up to size `n`.
    fn deleted(&self, n: usize) -> &[T];

    /// Get a reference to the first item.
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

/// Finite domains of unsigned integers.
pub mod uint {
    use std::cmp::Ord;
    use std::collections::BTreeMap;
    use std::fmt;

    use super::{Domain, DomainIterator};

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

        // TODO: move to the trait, if possible
        pub fn delete_if(&mut self, mut f: impl FnMut(&T) -> bool) {
            for i in 0..self.len {
                let x = self.dom[i]; // copy
                if f(&x) {
                    self.delete(&x);
                }
            }
        }

        #[allow(dead_code)]
        pub fn first(&self) -> Option<T> {
            self.dom.get(0).copied()
        }

        // TODO: track minimum element across deletions
        // to avoid this linear scan.
        #[allow(dead_code)]
        pub fn min(&self) -> Option<T> {
            self.dom[0..self.len].iter().min().copied()
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
            assert!(self.len <= self.dom.len());
            assert_eq!(self.dom.len(), self.map.len());

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
            assert!(self.len <= self.dom.len());
            assert_eq!(self.dom.len(), self.map.len());

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

    #[test]
    fn sparse_integer_set() {
        let mut dom = SparseIntegerSet::new(0..7);
        assert!(!dom.contains(&7));
        assert_eq!(
            dom.iter().copied().collect::<Vec<_>>(),
            vec![0, 1, 2, 3, 4, 5, 6]
        );
        assert_eq!(dom.min(), Some(0));
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

/// Finite domains of arbitrary (hashable) elements.
pub mod hash {
    use std::collections::HashMap;
    use std::fmt;
    use std::hash::{Hash, Hasher};

    use super::{Domain, DomainIterator};

    /// A sparse set of hashable objects.
    #[derive(Clone, Eq, PartialEq)]
    pub struct SparseHashSet<T: Hash + Eq> {
        dom: Vec<T>,
        map: HashMap<T, usize>,
        len: usize,
    }

    impl<T: Clone + Hash + Eq> SparseHashSet<T> {
        pub fn new(elements: impl IntoIterator<Item = T>) -> Self {
            let dom = elements.into_iter().collect::<Vec<T>>();
            let len = dom.len();
            let map = dom
                .iter()
                .cloned()
                .enumerate()
                .map(|(i, x)| (x, i))
                .collect::<HashMap<T, usize>>();
            Self { dom, map, len }
        }
    }

    impl<T: Hash + Eq + fmt::Debug> fmt::Debug for SparseHashSet<T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_set().entries(self.dom[0..self.len].iter()).finish()
        }
    }

    impl<T: Hash + Eq + fmt::Display> fmt::Display for SparseHashSet<T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                f,
                "{{{}}}",
                &self.dom[0..self.len]
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<String>>()
                    .join(" "),
            )
        }
    }

    impl<T> Domain<T> for SparseHashSet<T>
    where
        T: Clone + Hash + Eq,
    {
        fn contains(&self, x: &T) -> bool {
            self.map.get(x).map(|&i| i < self.len).unwrap_or(false)
        }

        fn delete(&mut self, x: &T) -> bool {
            assert!(self.len <= self.dom.len());
            assert_eq!(self.dom.len(), self.map.len());

            let i = self.map.get(x).map(|&i| i).unwrap_or(self.len);
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
            assert!(self.len <= self.dom.len());
            assert_eq!(self.dom.len(), self.map.len());

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

    impl<T: Hash + Eq> Hash for SparseHashSet<T> {
        fn hash<H: Hasher>(&self, state: &mut H) {
            Hash::hash(&self.dom[..self.len], state)
        }
    }

    #[test]
    fn sparse_hash_set() {
        #[derive(Clone, Debug, PartialEq, Eq, Hash)]
        struct Foo(&'static str);
        let a = Foo("a");
        let b = Foo("b");
        let c = Foo("c");
        let d = Foo("d");
        let mut dom = SparseHashSet::new([a.clone(), b.clone(), c.clone()]);
        assert_eq!(dom.iter().collect::<Vec<_>>(), vec![&a, &b, &c]);
        for x in [&a, &b, &c] {
            assert!(dom.contains(x));
            assert!(dom.delete(x));
            assert!(!dom.contains(x));
        }
        assert!(!dom.contains(&d));
        assert!(!dom.delete(&d));
        assert!(dom.is_empty());
        assert!(dom.iter().next().is_none());
        assert!(dom.restore(3));
        assert!(!dom.restore(7));
        assert_eq!(dom.iter().collect::<Vec<_>>(), vec![&c, &b, &a]);
    }
}
