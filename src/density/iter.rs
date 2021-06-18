//! Defines the `IntoIter` owned iterator for `D`.

use crate::{D, P};
use core::iter::FusedIterator;
use num_traits::identities::{One, Zero};
use std::ops::Range;

/// A by-value [array] iterator.
#[derive(Debug, Clone)]
pub struct IntoIter<T, const N: usize>
where
    T: PartialOrd + Zero + One,
{
    data: [P<T>; N],
    alive: Range<usize>,
}

impl<T, const N: usize> IntoIter<T, N>
where
    T: PartialOrd + Zero + One,
{
    pub fn new(d: D<T, N>) -> Self {
        Self {
            data: d.into_inner(),
            alive: 0..N,
        }
    }
}

impl<T, const N: usize> Iterator for IntoIter<T, N>
where
    T: PartialOrd + Zero + One + Clone,
{
    type Item = P<T>;
    fn next(&mut self) -> Option<Self::Item> {
        self.alive.next().map(|idx| self.data[idx].clone())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }

    fn count(self) -> usize {
        self.len()
    }

    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<T, const N: usize> DoubleEndedIterator for IntoIter<T, N>
where
    T: PartialOrd + Zero + One + Clone,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.alive.next_back().map(|idx| self.data[idx].clone())
    }
}

impl<T, const N: usize> ExactSizeIterator for IntoIter<T, N>
where
    T: PartialOrd + Zero + One + Clone,
{
    fn len(&self) -> usize {
        self.alive.end - self.alive.start
    }
}

impl<T, const N: usize> FusedIterator for IntoIter<T, N> where T: PartialOrd + Zero + One + Clone {}
