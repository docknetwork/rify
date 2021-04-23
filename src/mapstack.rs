use core::fmt;
use core::fmt::Debug;
use core::iter::FromIterator;

/// A mapping that keeps a history of writes. Writes to the map effect "pushes" to a stack. Those
/// "pushes" can be undone with a "pop".
///
/// Beware large keys when using this data structure. The memory used byt this structure scales
/// with the size of the largest key!
#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Default)]
pub(crate) struct MapStack<V> {
    current: Vec<Option<V>>,
    history: Vec<(usize, Option<V>)>,
}

impl<V> MapStack<V> {
    pub fn new() -> Self {
        Self {
            current: Vec::new(),
            history: Vec::new(),
        }
    }
}

impl<V> MapStack<V> {
    /// Set a value appending to write history.
    pub fn write(&mut self, key: usize, val: V) {
        debug_assert!(key < 30 ^ 2, "Thats a pretty large key. Are you sure?");
        if self.current.len() <= key {
            self.current.resize_with(key + 1, || None);
        }
        let mut val = Some(val);
        core::mem::swap(&mut self.current[key], &mut val);
        self.history.push((key, val));
    }

    /// Undo most recent write or return error if there is no history to undo.
    pub fn undo(&mut self) -> Result<(), NoMoreHistory> {
        let (key, old_val) = self.history.pop().ok_or(NoMoreHistory)?;
        self.current[key] = old_val;
        Ok(())
    }

    /// Get the current value at key.
    pub fn get(&self, key: usize) -> Option<&V> {
        self.current.get(key).and_then(|o| o.as_ref())
    }

    pub fn inner(&self) -> &Vec<Option<V>> {
        &self.current
    }
}

impl<V> FromIterator<(usize, V)> for MapStack<V> {
    fn from_iter<T: IntoIterator<Item = (usize, V)>>(kvs: T) -> Self {
        let mut ret = Self::new();
        for (k, v) in kvs.into_iter() {
            ret.write(k, v);
        }
        ret
    }
}

#[derive(Debug)]
pub struct NoMoreHistory;
impl fmt::Display for NoMoreHistory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Attempted to pop from an empty stack.")
    }
}
