use crate::reasoner::Quad;
use crate::rule::Rule;
use crate::translator::Translator;
use crate::Entity;
use crate::RuleApplication;
use alloc::collections::BTreeMap;
use core::fmt::Debug;

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

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
/// A proof element that has yet to be translated to a presentable form.
///
/// [crate::prove::prove] function does not immediately convert LowRuleApplication's to
/// [RuleApplication]'s. Rather, it converts only the LowRuleApplication's it is going to return
/// to the caller.
pub(crate) struct LowRuleApplication {
    pub rule_index: usize,
    pub instantiations: Vec<Option<usize>>,
}

impl LowRuleApplication {
    /// Translate to a higher representation [RuleApplication]. The higher representation is
    /// portable to other machines as long as those machines assume the same rule list.
    /// This lower representation is not portable.
    ///
    /// Panics
    ///
    /// This function will panic if:
    ///   - an unbound item from originial_rule is not instatiated by self
    ///   - or there is no translation for a global instatiation of one of the unbound entities in
    ///     original_rule.
    pub fn raise<Unbound: Ord, Bound: Ord + Clone>(
        &self,
        original_rule: &Rule<Unbound, Bound>,
        trans: &Translator<Bound>,
    ) -> RuleApplication<Bound> {
        let mut instantiations = Vec::new();

        // unbound_human -> unbound_local
        let uhul: BTreeMap<&Unbound, usize> = original_rule
            .cononical_unbound()
            .enumerate()
            .map(|(i, a)| (a, i))
            .collect();

        for unbound_human in original_rule.cononical_unbound() {
            let unbound_local: usize = uhul[unbound_human];
            let bound_global: usize = self.instantiations.get(unbound_local).unwrap().unwrap();
            let bound_human: &Bound = trans.back(bound_global).unwrap();
            instantiations.push(bound_human.clone());
        }

        RuleApplication {
            rule_index: self.rule_index,
            instantiations,
        }
    }
}

/// Attempt to forward translate a quad.
/// This is a helper function. It translates all four element of a quad, calling
/// [Translator::forward] for each element. If any element has no translation
/// this function will return `None`.
pub(crate) fn forward<T: Ord>(translator: &Translator<T>, key: &[T; 4]) -> Option<Quad> {
    let [s, p, o, g] = key;
    Some(
        [
            translator.forward(s)?,
            translator.forward(p)?,
            translator.forward(o)?,
            translator.forward(g)?,
        ]
        .into(),
    )
}

/// Reverse of [forward].
/// [forward] translates each element from `T` to `usize`. This function translates each element
/// from `usize` to `T`. If any element has no translation this function will return `None`.
pub(crate) fn back<T: Ord>(translator: &Translator<T>, key: Quad) -> Option<[&T; 4]> {
    let Quad { s, p, o, g } = key;
    Some([
        translator.back(s.0)?,
        translator.back(p.0)?,
        translator.back(o.0)?,
        translator.back(g.0)?,
    ])
}

/// list with repetition all bound vertices of rules and all verticies of premises
pub fn vertices<'a, 'b, 'c, Bound, Unbound>(
    premises: &'a [[Bound; 4]],
    rules: &'b [Rule<Unbound, Bound>],
) -> impl Iterator<Item = &'c Bound>
where
    'a: 'c,
    'b: 'c,
{
    rules
        .iter()
        .flat_map(|rule| rule.iter_entities().filter_map(Entity::as_bound))
        .chain(premises.iter().flatten())
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
