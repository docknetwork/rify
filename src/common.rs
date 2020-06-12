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
/// shorthand for Entity::Any
pub fn any<Unbound, Bound>(a: Unbound) -> crate::rule::Entity<Unbound, Bound> {
    crate::rule::Entity::Any(a)
}

#[cfg(test)]
/// shorthand for Entity::Exactly
pub fn exa<Unbound, Bound>(a: Bound) -> crate::rule::Entity<Unbound, Bound> {
    crate::rule::Entity::Exactly(a)
}
