//! Streams of lexical tokens.

use std::iter::Enumerate;
use std::ops::{Range, RangeFrom, RangeFull, RangeTo};

use nom::{InputIter, InputLength, InputTake, Needed, Slice, UnspecializedInput};

/// A generic collection of references to tokens.
/// Implements the traits needed to act as a
/// [nom](https://crates.io/crates/nom)
/// [custom input type](https://github.com/rust-bakery/nom/blob/main/doc/custom_input_types.md).
/// Adapted from the homonymous structure in Monkey.
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Tokens<'a, T> {
    pub tok: &'a [T],
    pub start: usize,
    pub end: usize,
}

impl<'a, T> Tokens<'a, T> {
    pub fn new(vec: &'a [T]) -> Self {
        Tokens {
            tok: vec,
            start: 0,
            end: vec.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }
}

impl<'a, T> InputLength for Tokens<'a, T> {
    #[inline]
    fn input_len(&self) -> usize {
        self.tok.len()
    }
}

impl<'a, T> InputTake for Tokens<'a, T> {
    #[inline]
    fn take(&self, count: usize) -> Self {
        Tokens {
            tok: &self.tok[0..count],
            start: 0,
            end: count,
        }
    }

    #[inline]
    fn take_split(&self, count: usize) -> (Self, Self) {
        let (prefix, suffix) = self.tok.split_at(count);
        let first = Tokens {
            tok: prefix,
            start: 0,
            end: prefix.len(),
        };
        let second = Tokens {
            tok: suffix,
            start: 0,
            end: suffix.len(),
        };
        (second, first)
    }
}

impl<'a, T> Slice<Range<usize>> for Tokens<'a, T> {
    #[inline]
    fn slice(&self, range: Range<usize>) -> Self {
        Tokens {
            tok: self.tok.slice(range.clone()),
            start: self.start + range.start,
            end: self.start + range.end,
        }
    }
}

impl<'a, T> Slice<RangeTo<usize>> for Tokens<'a, T> {
    #[inline]
    fn slice(&self, range: RangeTo<usize>) -> Self {
        self.slice(0..range.end)
    }
}

impl<'a, T> Slice<RangeFrom<usize>> for Tokens<'a, T> {
    #[inline]
    fn slice(&self, range: RangeFrom<usize>) -> Self {
        self.slice(range.start..self.end - self.start)
    }
}

impl<'a, T> Slice<RangeFull> for Tokens<'a, T> {
    #[inline]
    fn slice(&self, _: RangeFull) -> Self {
        Tokens {
            tok: self.tok,
            start: self.start,
            end: self.end,
        }
    }
}

impl<'a, T> InputIter for Tokens<'a, T> {
    type Item = &'a T;
    type Iter = Enumerate<::std::slice::Iter<'a, T>>;
    type IterElem = ::std::slice::Iter<'a, T>;

    #[inline]
    fn iter_indices(&self) -> Enumerate<::std::slice::Iter<'a, T>> {
        self.tok.iter().enumerate()
    }

    #[inline]
    fn iter_elements(&self) -> ::std::slice::Iter<'a, T> {
        self.tok.iter()
    }

    #[inline]
    fn position<P>(&self, predicate: P) -> Option<usize>
    where
        P: Fn(Self::Item) -> bool,
    {
        self.tok.iter().position(predicate)
    }

    #[inline]
    fn slice_index(&self, count: usize) -> Result<usize, Needed> {
        if self.tok.len() >= count {
            Ok(count)
        } else {
            Err(Needed::Unknown)
        }
    }
}

impl<'a, T> UnspecializedInput for Tokens<'a, T> {}

#[cfg(feature = "to-rust")]
mod to_rust {
    use proc_macro2::Span;

    use crate::lexer::Token;

    use super::*;

    impl<'a, T: Clone> Tokens<'a, Token<T, Span>> {
        pub fn span_first(&self) -> Option<Span> {
            self.iter_elements().next().map(|t| t.source)
        }

        pub fn span_last(&self) -> Option<Span> {
            self.iter_elements().last().map(|t| t.source)
        }

        pub fn span(&self) -> Option<Span> {
            // Needs experimental `proc_macro::Span::join` to produce whole span.
            self.span_first()
        }
    }
}
