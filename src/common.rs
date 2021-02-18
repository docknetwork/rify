/// Increment argument then return previous value.
///
/// ```nocompile
/// let mut a = 0;
/// assert_eq!(inc(&mut a), 0);
/// assert_eq!(a, 1);
/// assert_eq!(inc(&mut a), 1);
/// assert_eq!(a, 2);
/// assert_eq!(inc(&mut a), 2);
/// assert_eq!(a, 3);
/// ```
pub fn inc<T: core::ops::AddAssign>(a: &mut T) -> T
where
    T: core::ops::AddAssign + Clone,
    u8: Into<T>,
{
    let ret = a.clone();
    *a += 1u8.into();
    ret
}

#[cfg(test)]
mod test_util {
    use core::fmt::Debug;

    pub fn decl_rules<Unbound: Ord + Debug + Clone, Bound: Ord + Clone>(
        rs: &[[&[[crate::rule::Entity<Unbound, Bound>; 4]]; 2]],
    ) -> Vec<crate::rule::Rule<Unbound, Bound>> {
        rs.iter()
            .map(|[ifa, then]| crate::rule::Rule::create(ifa.to_vec(), then.to_vec()).unwrap())
            .collect()
    }
}

#[cfg(test)]
pub use test_util::*;
