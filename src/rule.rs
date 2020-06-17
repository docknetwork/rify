//! The reasoner's rule representation is optimized machine use, not human use. Comprehending and
//! composing rules directly is difficult for humans. This module provides a human friendly rule
//! description datatype that can be lowered to the reasoner's rule representation.

use crate::common::inc;
use crate::reasoner::{self, Triple};
use crate::translator::Translator;
use crate::Claim;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::fmt::Debug;
use core::fmt::Display;

#[derive(Clone, Debug, PartialEq, Eq)]
// invariants held:
//   unbound names may not exists in `then` unless they exist also in `if_all`
//
// TODO: find a way to make fields non-public to protect invariant
pub(crate) struct LowRule {
    pub if_all: Vec<Triple>,            // contains locally scoped names
    pub then: Vec<Triple>,              // contains locally scoped names
    pub inst: reasoner::Instantiations, // partially maps the local scope to some global scope
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub enum Entity<Unbound, Bound> {
    Any(Unbound),
    Exactly(Bound),
}

impl<Unbound, Bound> Entity<Unbound, Bound> {
    pub fn as_unbound(&self) -> Option<&Unbound> {
        match self {
            Entity::Any(s) => Some(s),
            Entity::Exactly(_) => None,
        }
    }

    pub fn as_bound(&self) -> Option<&Bound> {
        match self {
            Entity::Any(_) => None,
            Entity::Exactly(s) => Some(s),
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
// invariants held:
//   unbound names may not exists in `then` unless they exist also in `if_all`
pub struct Rule<Unbound, Bound> {
    if_all: Vec<Claim<Entity<Unbound, Bound>>>,
    then: Vec<Claim<Entity<Unbound, Bound>>>,
}

impl<'a, Unbound: Ord + Clone, Bound: Ord> Rule<Unbound, Bound> {
    pub fn create(
        if_all: Vec<Claim<Entity<Unbound, Bound>>>,
        then: Vec<Claim<Entity<Unbound, Bound>>>,
    ) -> Result<Self, InvalidRule<Unbound>> {
        let unbound_if = if_all.iter().flatten().filter_map(Entity::as_unbound);
        let unbound_then = then.iter().flatten().filter_map(Entity::as_unbound);

        for th in unbound_then.clone() {
            if !unbound_if.clone().any(|ifa| ifa == th) {
                return Err(InvalidRule::UnboundImplied(th.clone()));
            }
        }

        Ok(Self { if_all, then })
    }

    pub(crate) fn lower(&self, tran: &Translator<Bound>) -> Result<LowRule, NoTranslation<&Bound>> {
        // There are three types of name at play here.
        // - human names are represented as Entities
        // - local names are local to the rule we are creating. they are represented as u32
        // - global names are from the translator. they are represented as u32

        // assign local names to each human name
        // local names will be in a continous range from 0.
        // smaller local names will represent unbound entities, larger ones will represent bound
        let mut next_local = 0u32;
        let unbound_map = {
            let mut unbound_map: BTreeMap<&Unbound, u32> = BTreeMap::new();
            for unbound in self.if_all.iter().flatten().filter_map(Entity::as_unbound) {
                unbound_map
                    .entry(&unbound)
                    .or_insert_with(|| inc(&mut next_local));
            }
            unbound_map
        };
        let bound_map = {
            let mut bound_map: BTreeMap<&Bound, u32> = BTreeMap::new();
            for bound in self.iter_entities().filter_map(Entity::as_bound) {
                bound_map
                    .entry(&bound)
                    .or_insert_with(|| inc(&mut next_local));
            }
            bound_map
        };
        debug_assert!(
            bound_map.values().all(|bound_local| unbound_map
                .values()
                .all(|unbound_local| bound_local > unbound_local)),
            "unbound names are smaller than bound names"
        );
        debug_assert_eq!(
            (0..next_local).collect::<BTreeSet<u32>>(),
            unbound_map
                .values()
                .chain(bound_map.values())
                .cloned()
                .collect(),
            "no names slots are wasted"
        );
        debug_assert_eq!(
            next_local as usize,
            unbound_map.values().chain(bound_map.values()).count(),
            "no duplicate assignments"
        );
        debug_assert!(self
            .if_all
            .iter()
            .flatten()
            .filter_map(Entity::as_unbound)
            .all(|unbound_then| { unbound_map.contains_key(&unbound_then) }));

        // gets the local name for a human_name
        let local_name = |entity: &Entity<Unbound, Bound>| -> u32 {
            match entity {
                Entity::Any(s) => unbound_map[s],
                Entity::Exactly(s) => bound_map[s],
            }
        };
        // converts a human readable restriction list to a list of locally scoped machine oriented
        // restrictions
        let to_requirements = |hu: &[Claim<Entity<Unbound, Bound>>]| -> Vec<Triple> {
            hu.iter()
                .map(|[s, p, o]| Triple::from_tuple(local_name(&s), local_name(&p), local_name(&o)))
                .collect()
        };

        Ok(LowRule {
            if_all: to_requirements(&self.if_all),
            then: to_requirements(&self.then),
            inst: bound_map
                .iter()
                .map(|(human_name, local_name)| {
                    let global_name = tran.forward(human_name).ok_or(NoTranslation(*human_name))?;
                    Ok((*local_name, global_name))
                })
                .collect::<Result<_, _>>()?,
        })
    }
}

impl<'a, Unbound: Ord, Bound> Rule<Unbound, Bound> {
    /// List the unique unbound names in this rule in order of appearance.
    pub(crate) fn cononical_unbound(&self) -> impl Iterator<Item = &Unbound> {
        let mut listed = BTreeSet::<&Unbound>::new();
        self.if_all
            .iter()
            .flatten()
            .filter_map(Entity::as_unbound)
            .filter_map(move |unbound| {
                if listed.contains(unbound) {
                    None
                } else {
                    listed.insert(unbound);
                    Some(unbound)
                }
            })
    }
}

impl<'a, Unbound, Bound> Rule<Unbound, Bound> {
    pub fn iter_entities(&self) -> impl Iterator<Item = &Entity<Unbound, Bound>> {
        self.if_all.iter().chain(self.then.iter()).flatten()
    }

    pub(crate) fn if_all(&self) -> &[Claim<Entity<Unbound, Bound>>] {
        &self.if_all
    }

    pub(crate) fn then(&self) -> &[Claim<Entity<Unbound, Bound>>] {
        &self.then
    }
}

#[derive(Debug)]
pub enum InvalidRule<Unbound> {
    /// Implied statements (part of the "then" property) must not contain unbound symbols that do
    /// not exist in the other side of the expression.
    ///
    /// Examples of rules that would cause this error:
    ///
    /// ```customlang
    /// // all statements are true
    /// -> (?a, ?a, ?a)
    ///
    /// // conditional universal statement
    /// (<sun> <enabled> <false>) -> (?a <color> <black>)
    /// ```
    UnboundImplied(Unbound),
}

impl<Unbound: Debug> Display for InvalidRule<Unbound> {
    fn fmt(&self, fmtr: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        Debug::fmt(self, fmtr)
    }
}

#[cfg(feature = "std")]
impl<Unbound> std::error::Error for InvalidRule<Unbound> where InvalidRule<Unbound>: Debug + Display {}

#[derive(Debug, Eq, PartialEq)]
/// The rule contains terms that have no corresponding entity in the translators target universe.
pub struct NoTranslation<T>(T);

#[cfg(test)]
mod test {
    use super::*;
    use crate::common::{Any, Exa};
    use core::iter::FromIterator;

    #[test]
    fn similar_names() {
        // test rule
        // (?a <a> <b>) ->
        // ?a should be a separate entity from <a>

        let rule = Rule::<&str, &str> {
            if_all: vec![[Any("a"), Exa("a"), Any("b")]],
            then: vec![],
        };
        let trans: Translator<&str> = ["a"].iter().cloned().collect();
        let rr = rule.lower(&trans).unwrap();

        // ?a != <a>
        assert_ne!(rr.if_all[0].subject.0, rr.if_all[0].property.0);
    }

    #[test]
    fn lower() {
        // rules: (?a parent ?b) -> (?a ancestor ?b)
        //        (?a ancestor ?b) and (?b ancestor ?c) -> (?a ancestor ?c)

        let trans: Translator<&str> = ["parent", "ancestor"].iter().cloned().collect();

        {
            let rulea = Rule::<u16, &str> {
                if_all: vec![[Any(0xa), Exa("parent"), Any(0xb)]],
                then: vec![[Any(0xa), Exa("ancestor"), Any(0xb)]],
            };

            let re_rulea = rulea.lower(&trans).unwrap();
            let keys = [
                re_rulea.if_all[0].subject.0,
                re_rulea.if_all[0].property.0,
                re_rulea.if_all[0].object.0,
                re_rulea.then[0].subject.0,
                re_rulea.then[0].property.0,
                re_rulea.then[0].object.0,
            ];
            let vals: Vec<Option<Option<&&str>>> = keys
                .iter()
                .map(|local_name| {
                    re_rulea
                        .inst
                        .as_ref()
                        .get(&local_name)
                        .map(|global_name| trans.back(*global_name))
                })
                .collect();
            assert_eq!(
                &vals,
                &[
                    None,
                    Some(Some(&"parent")),
                    None,
                    None,
                    Some(Some(&"ancestor")),
                    None,
                ]
            );

            let ifa = re_rulea.if_all;
            let then = re_rulea.then;
            assert_ne!(ifa[0].property.0, then[0].property.0); // "parent" != "ancestor"
            assert_eq!(ifa[0].subject.0, then[0].subject.0); // a == a
            assert_eq!(ifa[0].object.0, then[0].object.0); // b == b
        }

        {
            let ruleb = Rule::<&str, &str> {
                if_all: vec![
                    [Any("a"), Exa("ancestor"), Any("b")],
                    [Any("b"), Exa("ancestor"), Any("c")],
                ],
                then: vec![[Any("a"), Exa("ancestor"), Any("c")]],
            };

            let re_ruleb = ruleb.lower(&trans).unwrap();
            let keys = [
                re_ruleb.if_all[0].subject.0,
                re_ruleb.if_all[0].property.0,
                re_ruleb.if_all[0].object.0,
                re_ruleb.if_all[1].subject.0,
                re_ruleb.if_all[1].property.0,
                re_ruleb.if_all[1].object.0,
                re_ruleb.then[0].subject.0,
                re_ruleb.then[0].property.0,
                re_ruleb.then[0].object.0,
            ];
            let vals: Vec<Option<Option<&&str>>> = keys
                .iter()
                .map(|local_name| {
                    re_ruleb
                        .inst
                        .as_ref()
                        .get(&local_name)
                        .map(|global_name| trans.back(*global_name))
                })
                .collect();
            assert_eq!(
                &vals,
                &[
                    None,
                    Some(Some(&"ancestor")),
                    None,
                    None,
                    Some(Some(&"ancestor")),
                    None,
                    None,
                    Some(Some(&"ancestor")),
                    None,
                ]
            );

            let ifa = re_ruleb.if_all;
            let then = re_ruleb.then;
            assert_ne!(ifa[0].subject.0, ifa[1].subject.0); // a != b
            assert_ne!(ifa[0].object.0, then[0].object.0); // b != c

            // "ancestor" == "ancestor" == "ancestor"
            assert_eq!(ifa[0].property.0, ifa[1].property.0);
            assert_eq!(ifa[1].property.0, then[0].property.0);

            assert_eq!(ifa[0].subject.0, then[0].subject.0); // a == a
            assert_eq!(ifa[1].object.0, then[0].object.0); // b == b
        }
    }

    #[test]
    fn lower_no_translation_err() {
        let trans = Translator::<&str>::from_iter(vec![]);

        let r = Rule::create(vec![[Any("a"), Exa("unknown"), Any("b")]], vec![]).unwrap();
        let err = r.lower(&trans).unwrap_err();
        assert_eq!(err, NoTranslation(&"unknown"));

        let r = Rule::<&str, &str>::create(
            vec![],
            vec![[Exa("unknown"), Exa("unknown"), Exa("unknown")]],
        )
        .unwrap();
        let err = r.lower(&trans).unwrap_err();
        assert_eq!(err, NoTranslation(&"unknown"));
    }

    #[test]
    fn create_invalid() {
        Rule::<&str, &str>::create(vec![], vec![[Any("a"), Any("a"), Any("a")]]).unwrap_err();
    }
}
