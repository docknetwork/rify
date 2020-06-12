//! The reasoner's rule representation is optimized machine use, not human use. Comprehending and
//! composing rules directly is difficult for humans. This module provides a human friendly rule
//! description datatype that can be lowered to the reasoner's rule representation.

use crate::common::inc;
use crate::reasoner::{self, Triple};
use crate::translator::Translator;
use alloc::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq)]
// invariants held:
//   unbound names may not exists in `then` unless they exist also in `if_all`
//
// TODO: find a way to make fields non-public to protect invariant
pub struct ReasonersRule {
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
pub struct Rule<'a, Unbound, Bound> {
    if_all: &'a [[Entity<Unbound, Bound>; 3]],
    then: &'a [[Entity<Unbound, Bound>; 3]],
}

impl<'a, Unbound: Ord, Bound: Ord> Rule<'a, Unbound, Bound> {
    pub fn create(
        if_all: &'a [[Entity<Unbound, Bound>; 3]],
        then: &'a [[Entity<Unbound, Bound>; 3]],
    ) -> Result<Self, InvalidRule<&'a Unbound>> {
        let unbound_if = if_all.iter().flatten().filter_map(Entity::as_unbound);
        let unbound_then = then.iter().flatten().filter_map(Entity::as_unbound);

        for th in unbound_then.clone() {
            if !unbound_if.clone().any(|ifa| ifa == th) {
                return Err(InvalidRule::UnboundImplied(th));
            }
        }

        Ok(Self { if_all, then })
    }

    pub fn to_reasoners_rule(
        &self,
        tran: &Translator<Bound>,
    ) -> Result<ReasonersRule, NoTranslation<&Bound>> {
        // There are three types of name at play here.
        // - human names are represented as Entities
        // - local names are local to the rule we are creating. they are represented as u32
        // - global names are from the translator. they are represented as u32

        // assign local names to each human name
        let mut next_local = 0u32;
        let unbound_map: BTreeMap<&Unbound, u32> = self
            .if_all
            .iter()
            .flatten()
            .filter_map(Entity::as_unbound)
            .map(|s| (s, inc(&mut next_local)))
            .collect();
        let bound_map: BTreeMap<&Bound, u32> = self
            .iter_entities()
            .filter_map(Entity::as_bound)
            .map(|s| (s, inc(&mut next_local)))
            .collect();

        // gets the local name for a human_name
        let local_name = |entity: &Entity<Unbound, Bound>| -> u32 {
            match entity {
                Entity::Any(s) => unbound_map[s],
                Entity::Exactly(s) => bound_map[s],
            }
        };
        // converts a human readable restriction list to a list of locally scoped machine oriented
        // restrictions
        let to_requirements = |hu: &[[Entity<Unbound, Bound>; 3]]| -> Vec<Triple> {
            hu.iter()
                .map(|[s, p, o]| Triple::from_tuple(local_name(&s), local_name(&p), local_name(&o)))
                .collect()
        };

        Ok(ReasonersRule {
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

    pub fn iter_entities(&self) -> impl Iterator<Item = &Entity<Unbound, Bound>> {
        self.if_all.iter().chain(self.then).flatten()
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

#[derive(Debug, Eq, PartialEq)]
/// The rule contains terms that have no corresponding entity in the translators target universe.
pub struct NoTranslation<T>(T);

#[cfg(test)]
mod test {
    use super::*;
    use crate::common::{any, exa};
    use core::iter::FromIterator;

    #[test]
    fn similar_names() {
        // test rule
        // (?a <a> <b>) ->
        // ?a should be a separate entity from <a>

        let rule = Rule::<&str, &str> {
            if_all: &[[any("a"), exa("a"), any("b")]],
            then: &[],
        };
        let trans: Translator<&str> = ["a"].iter().cloned().collect();
        let rr = rule.to_reasoners_rule(&trans).unwrap();

        // ?a != <a>
        assert_ne!(rr.if_all[0].subject.0, rr.if_all[0].property.0);
    }

    #[test]
    fn to_reasoners_rule() {
        // rules: (?a parent ?b) -> (?a ancestor ?b)
        //        (?a ancestor ?b) and (?b ancestor ?c) -> (?a ancestor ?c)

        let trans: Translator<&str> = ["parent", "ancestor"].iter().cloned().collect();

        {
            let rulea = Rule::<u16, &str> {
                if_all: &[[any(0xa), exa("parent"), any(0xb)]],
                then: &[[any(0xa), exa("ancestor"), any(0xb)]],
            };

            let re_rulea = rulea.to_reasoners_rule(&trans).unwrap();
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
                if_all: &[
                    [any("a"), exa("ancestor"), any("b")],
                    [any("b"), exa("ancestor"), any("c")],
                ],
                then: &[[any("a"), exa("ancestor"), any("c")]],
            };

            let re_ruleb = ruleb.to_reasoners_rule(&trans).unwrap();
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
    fn to_reasoners_rule_no_translation_err() {
        let trans = Translator::<&str>::from_iter(vec![]);

        let r = Rule::<&str, &str>::create(
            &[[
                Entity::Any("a"),
                Entity::Exactly("unknown"),
                Entity::Any("b"),
            ]],
            &[],
        )
        .unwrap();
        let err = r.to_reasoners_rule(&trans).unwrap_err();
        assert_eq!(err, NoTranslation(&"unknown"));

        let r = Rule::<&str, &str>::create(
            &[],
            &[[
                Entity::Exactly("unknown"),
                Entity::Exactly("unknown"),
                Entity::Exactly("unknown"),
            ]],
        )
        .unwrap();
        let err = r.to_reasoners_rule(&trans).unwrap_err();
        assert_eq!(err, NoTranslation(&"unknown"));
    }

    #[test]
    fn create_invalid() {
        Rule::<&str, &str>::create(&[], &[[any("a"), any("a"), any("a")]]).unwrap_err();
    }
}
