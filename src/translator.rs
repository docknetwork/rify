//! The reasoner itself does not process RDF tuples directly. Instead the reasoner operates on
//! abstract entities. The only requirement for these entities is that they have some total
//! ordering (the reasoner needs to keep indices of entity relationships for efficient joins).
//! The reasoner represents these entities as usize. RDF entities are usually expressed as some
//! other type e.g. String. This module provides a way to generate and stores a mapping from
//! some type T to usize. The mapping is bijective (it goes both ways) so after reasoning is
//! performed, the results can be converted back to the original format with entities of type T.

use core::borrow::Borrow;
use core::iter::FromIterator;

/// bijective mapping from some type T to usize
#[derive(Debug)]
pub struct Translator<T> {
    /// represents both usize -> T and T -> usize
    widdershins: Box<[T]>,
}

impl<T: Ord> Translator<T> {
    /// lookup the entity representing t
    pub fn forward(&self, t: &impl Borrow<T>) -> Option<usize> {
        self.widdershins.binary_search(t.borrow()).ok()
    }

    /// lookup the t that the entity represents
    pub fn back(&self, a: usize) -> Option<&T> {
        self.widdershins.get(a)
    }
}

impl<T: Ord> FromIterator<T> for Translator<T> {
    fn from_iter<I: IntoIterator<Item = T>>(src: I) -> Self {
        let mut table: Vec<T> = src.into_iter().collect();
        table.sort_unstable();
        table.dedup();
        Self {
            widdershins: table.into_boxed_slice(),
        }
    }
}
