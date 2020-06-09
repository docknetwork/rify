//! The reasoner's rule representation is optimized machine use, not human use. Reading and writing
//! rules directly is difficult for humans. This module provides a human friendly rule description
//! datatype that can be lowered to the reasoner's rule representation.

use crate::reasoner;
use crate::translator::Translator;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::iter::once;
use core::ops::Not;

#[derive(Debug)]
pub struct ReasonersRule {
    pub if_all: Vec<reasoner::Triple>,
    pub then: Vec<reasoner::Triple>,
    pub inst: reasoner::Instantiations,
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub enum Entity<T> {
    Any(String),
    Exactly(T),
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct Restriction<T> {
    pub subject: Entity<T>,
    pub property: Entity<T>,
    pub object: Entity<T>,
}

pub struct Rule<T> {
    if_all: Vec<Restriction<T>>,
    then: Vec<Restriction<T>>,
}

impl<T: Ord> Rule<T> {
    pub fn create(
        if_all: Vec<Restriction<T>>,
        then: Vec<Restriction<T>>,
    ) -> Result<Rule<T>, InvalidRule> {
        let if_unbound: BTreeSet<&String> = iter_entities(&if_all).filter_map(as_unbound).collect();

        if iter_entities(&then)
            .filter_map(as_unbound)
            .all(|e| if_unbound.contains(e))
            .not()
        {
            return Err(InvalidRule::UnboundImplied);
        }

        Ok(Self { if_all, then })
    }

    pub fn to_reasoners_rule(
        &self,
        tran: &Translator<T>,
    ) -> Result<ReasonersRule, NoTranslation<T>> {
        // There are three dimensions of name at play here.
        // - human names are represented as Entities
        // - local names are local to the rule we are creating. they are represented as u32
        // - global names are from the translator. they are represented as u32

        // assign local names to each human name
        let mut next_local = 0u32;
        let unbound_map: BTreeMap<&String, u32> = iter_entities(&self.if_all)
            .filter_map(as_unbound)
            .map(|s| (s, inc(&mut next_local)))
            .collect();
        let bound_map: BTreeMap<&T, u32> = iter_entities(&self.if_all)
            .chain(iter_entities(&self.then))
            .filter_map(as_bound)
            .map(|s| (s, inc(&mut next_local)))
            .collect();

        // gets the local name for an human named entity
        let local_name = |entity: &Entity<T>| -> u32 {
            match entity {
                Entity::Any(s) => unbound_map[s],
                Entity::Exactly(s) => bound_map[s],
            }
        };
        // converts a human readable restriction list to a locally scoped requirement list
        let to_requirements = |rest: &[Restriction<T>]| -> Vec<reasoner::Triple> {
            rest.iter()
                .map(|rest| {
                    reasoner::Triple::from_tuple(
                        local_name(&rest.subject),
                        local_name(&rest.property),
                        local_name(&rest.object),
                    )
                })
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

    pub fn from_reasoners_rule<'rr>(
        rr: &'rr ReasonersRule,
        trans: &Translator<T>,
        name_generator: &mut impl FnMut() -> T,
    ) -> Result<Self, NoTranslation<'rr, u32>> {
        unimplemented!()
    }
}

#[derive(Debug)]
pub enum InvalidRule {
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
    UnboundImplied,
}

#[derive(Debug)]
/// The rule contains terms that have no correspond entity in the translators target universe.
pub struct NoTranslation<'a, T>(&'a T);

fn as_unbound<T>(e: &Entity<T>) -> Option<&String> {
    match e {
        Entity::Any(s) => Some(s),
        Entity::Exactly(_) => None,
    }
}

fn as_bound<T>(e: &Entity<T>) -> Option<&T> {
    match e {
        Entity::Any(_) => None,
        Entity::Exactly(s) => Some(s),
    }
}

fn iter_entities<T>(res: &[Restriction<T>]) -> impl Iterator<Item = &Entity<T>> {
    res.iter().flat_map(|rule| {
        once(&rule.subject)
            .chain(once(&rule.property))
            .chain(once(&rule.object))
    })
}

/// increment argument then retune previous value
fn inc(a: &mut u32) -> u32 {
    *a += 1;
    *a - 1
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::mapstack::MapStack;
    use core::iter::FromIterator;

    #[test]
    fn similar_names() {
        // test rule
        // (?a <a> <b>) ->
        // ?a should be a separate entity from <a>

        let rule = Rule::<String> {
            if_all: vec![Restriction {
                subject: Entity::Any("a".into()),
                property: Entity::Exactly("a".into()),
                object: Entity::Any("b".into()),
            }],
            then: vec![],
        };
        let trans = Translator::<String>::from_iter(vec!["a".into()]);
        let rr = rule.to_reasoners_rule(&trans).unwrap();

        // ?a != <a>
        assert_ne!(rr.if_all[0].subject.0, rr.if_all[0].property.0);
    }

    #[test]
    fn to_reasoners_rule() {
        // rules: (?a parent ?b) -> (?a ancestor ?b)
        //        (?a ancestor ?b) and (?b ancestor ?c) -> (?a ancestor ?c)

        let trans = Translator::<&str>::from_iter(vec!["parent", "ancestor"]);

        {
            let rulea = Rule::<&str> {
                if_all: vec![Restriction {
                    subject: Entity::Any("a".into()),
                    property: Entity::Exactly("parent"),
                    object: Entity::Any("b".into()),
                }],
                then: vec![Restriction {
                    subject: Entity::Any("a".into()),
                    property: Entity::Exactly("ancestor"),
                    object: Entity::Any("b".into()),
                }],
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
            let ruleb = Rule::<&str> {
                if_all: vec![
                    Restriction {
                        subject: Entity::Any("a".into()),
                        property: Entity::Exactly("ancestor"),
                        object: Entity::Any("b".into()),
                    },
                    Restriction {
                        subject: Entity::Any("b".into()),
                        property: Entity::Exactly("ancestor"),
                        object: Entity::Any("c".into()),
                    },
                ],
                then: vec![Restriction {
                    subject: Entity::Any("a".into()),
                    property: Entity::Exactly("ancestor"),
                    object: Entity::Any("c".into()),
                }],
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
    fn from_reasoners_rule() {
        let trans = Translator::<String>::from_iter(vec!["ancestor".into()]);
        let rr = ReasonersRule {
            if_all: vec![
                reasoner::Triple::from_tuple(0, 6, 2),
                reasoner::Triple::from_tuple(2, 6, 3),
            ],
            then: vec![reasoner::Triple::from_tuple(0, 6, 3)],
            inst: MapStack::from_iter(vec![(6, 0)]),
        };

        let mut human_names = 0..;
        let rule = Rule::from_reasoners_rule(&rr, &trans, &mut || {
            format!("a{}", human_names.next().unwrap())
        })
        .unwrap();
    }

    #[test]
    fn to_from_reasoners_rule() {}
}
