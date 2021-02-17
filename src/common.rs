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
pub fn inc(a: &mut u32) -> u32 {
    *a += 1;
    *a - 1
}

#[cfg(test)]
mod test_util {
    use crate::rule::Entity;
    pub use crate::rule::Entity::{Bound, Unbound};
    use crate::rule::Rule;
    use crate::Claim;
    use core::fmt::Debug;

    pub fn decl_rules<Unbound: Ord + Debug + Clone, Bound: Ord + Clone>(
        rs: &[[&[Claim<Entity<Unbound, Bound>>]; 2]],
    ) -> Vec<Rule<Unbound, Bound>> {
        rs.iter()
            .map(|[ifa, then]| Rule::create(ifa.to_vec(), then.to_vec()).unwrap())
            .collect()
    }

    pub fn qdecl_rules<Unbound: Ord + Debug + Clone, Bound: Ord + Clone>(
        rs: &[[&[[crate::qrule::Entity<Unbound, Bound>; 4]]; 2]],
    ) -> Vec<crate::qrule::Rule<Unbound, Bound>> {
        rs.iter()
            .map(|[ifa, then]| crate::qrule::Rule::create(ifa.to_vec(), then.to_vec()).unwrap())
            .collect()
    }
}
#[cfg(test)]
pub use test_util::*;
