use core::cmp::Ordering;

/// A sorted Vec of unique elements.
pub struct VecSet<T> {
    sorted: Vec<T>,
}

impl<T> VecSet<T> {
    pub fn new() -> Self {
        Self { sorted: Vec::new() }
    }

    /// Insert a new element while maintaining the ordering defined by the comparator function.
    /// If the element already exists in the set according to the comparator it will not be
    /// inserted.
    pub fn insert(&mut self, a: T, f: impl Fn(&T, &T) -> Ordering) {
        match self.sorted.binary_search_by(|e| f(e, &a)) {
            Ok(_) => (),
            Err(i) => self.sorted.insert(i, a),
        }
    }

    /// Get the range for which the comparator function returns Ordering::Equal.
    ///
    /// The comparator function should implement an order consistent
    /// with the sort order of the underlying slice, returning an
    /// order code that indicates whether its argument is `Less`,
    /// `Equal` or `Greater` the desired target.
    pub fn range(&self, f: impl Fn(&T) -> Ordering) -> &[T] {
        let start = self
            .sorted
            .binary_search_by(|a| match f(a) {
                Ordering::Equal => Ordering::Greater,
                o => o,
            })
            .unwrap_err();
        let top = &self.sorted[start..]; // can optimize using unsafe
        let end = top
            .binary_search_by(|a| match f(a) {
                Ordering::Equal => Ordering::Less,
                o => o,
            })
            .unwrap_err();
        &top[..end] // can optimize using unsafe
    }

    /// Get a reference to the underlying array.
    pub fn as_slice(&self) -> &[T] {
        self.sorted.as_slice()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn vecset() {
        let ordering = |a: &u8, b: &u8| -> Ordering { a.cmp(&b) };
        let sub_ordering = |a: &u8, b: &u8| -> Ordering { (a / 2).cmp(&(b / 2)) };
        let mut vs: VecSet<u8> = VecSet::new();
        for n in &[32u8, 5, 2, 2, 4, 3, 2, 23, 24, 253] {
            vs.insert(*n, ordering);
        }
        assert_eq!(vs.as_slice(), [2, 3, 4, 5, 23, 24, 32, 253]);
        assert_eq!(vs.range(|a| ordering(a, &4)), [4]);
        assert_eq!(vs.range(|a| sub_ordering(a, &4)), [4, 5]);
        assert_eq!(vs.range(|a| sub_ordering(a, &2)), [2, 3]);
        assert_eq!(vs.range(|a| sub_ordering(a, &3)), [2, 3]);
    }
}
