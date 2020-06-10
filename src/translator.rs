//! The reasoner itself does not process RDF tuples directly. Instead the reasoner operates on
//! abstract entities. The only requirement for these entities is that they have some total
//! ordering (the reasoner needs to keep indices of entity relationships for efficient joins).
//! The reasoner represents these entities as u32. RDF entities are usually expressed as some
//! other type e.g. String. This module provides a way to generates and stores a mapping from
//! some type T to u32. The mapping is bijective (it goes both ways) so after reasoning is
//! performed, the results can be converted back to the original format with entities of type T.

use core::borrow::Borrow;
use core::convert::TryInto;
use core::iter::FromIterator;

/// bijective mapping from some type T to u32
#[derive(Debug)]
pub struct Translator<T> {
    /// represents both u32 -> T and T -> u32
    widdershins: Box<[T]>,
}

impl<T: Ord> Translator<T> {
    /// lookup the entity representing t
    pub fn forward(&self, t: &impl Borrow<T>) -> Option<u32> {
        debug_assert!(
            TryInto::<u32>::try_into(self.widdershins.len().saturating_sub(1)).is_ok(),
            "too many entities to represent as u32"
        );
        self.widdershins
            .binary_search(t.borrow())
            .ok()
            .map(|a: usize| a as u32)
    }

    /// lookup the t that the entity represents
    pub fn back(&self, a: u32) -> Option<&T> {
        self.widdershins.get(a as usize)
    }
}

// TODO: The user of this impl probably won't expect an implementaion of FromIterator to panic
//       This impl panics if there are too many elements to index with a u32.
impl<T: Ord> FromIterator<T> for Translator<T> {
    fn from_iter<I: IntoIterator<Item = T>>(src: I) -> Self {
        let mut table: Vec<T> = src.into_iter().collect();
        table.sort_unstable();
        table.dedup();
        assert!(
            TryInto::<u32>::try_into(table.len().saturating_sub(1)).is_ok(),
            "too many entities to represent as u32"
        );
        Self {
            widdershins: table.into_boxed_slice(),
        }
    }
}
