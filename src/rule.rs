//! The reasoner's rule representation is optimized machine use, not human use. Reading and writing
//! rules directly is difficult for humans. This module provides a human friendly rule description
//! datatype that can be lowered to the reasoner's rule representation.

use crate::reasoner;
use crate::translator::Translator;
use alloc::collections::{BTreeMap, BTreeSet};
use core::iter::once;

#[derive(Clone, Debug)]
// invariants held:
//   unbound names may not exists in `then` unless they exist also in `if_all`
pub struct ReasonersRule {
    if_all: Vec<reasoner::Triple>,  // contains locally scoped names
    then: Vec<reasoner::Triple>,    // contains locally scoped names
    inst: reasoner::Instantiations, // partially maps the local scope to some global scope
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub enum Entity<T> {
    Any(String),
    Exactly(T),
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct Restriction<T> {
    pub subject: Entity<T>,
    pub property: Entity<T>,
    pub object: Entity<T>,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
// invariants held:
//   unbound names may not exists in `then` unless they exist also in `if_all`
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

        for unbound in iter_entities(&then).filter_map(as_unbound) {
            if !if_unbound.contains(unbound) {
                return Err(InvalidRule::UnboundImplied(unbound.clone()));
            }
        }

        Ok(Self { if_all, then })
    }

    pub fn to_reasoners_rule(
        &self,
        tran: &Translator<T>,
    ) -> Result<ReasonersRule, NoTranslation<T>> {
        // There are three types of name at play here.
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

        // gets the local name for a human_name
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
        name_generator: &mut impl FnMut() -> String,
    ) -> Result<Self, NoTranslation<'rr, u32>>
    where
        T: Clone,
    {
        let uniq_local_names: BTreeSet<u32> = iter_local_reasoner_entities(&rr.if_all).collect();
        let local_to_human: BTreeMap<u32, Entity<T>> = uniq_local_names
            .iter()
            .map(
                |local_name| -> Result<(u32, Entity<T>), NoTranslation<'rr, u32>> {
                    let ent: Entity<T> = match rr.inst.as_ref().get(&local_name) {
                        Some(global_name) => Entity::Exactly(
                            trans
                                .back(*global_name)
                                .ok_or_else(|| NoTranslation(global_name))?
                                .clone(),
                        ),
                        None => Entity::Any(name_generator()),
                    };
                    Ok((*local_name, ent))
                },
            )
            .collect::<Result<_, _>>()?;
        let to_human = |triple: &reasoner::Triple| -> Restriction<T> {
            Restriction::<T> {
                subject: local_to_human[&triple.subject.0].clone(),
                property: local_to_human[&triple.property.0].clone(),
                object: local_to_human[&triple.object.0].clone(),
            }
        };
        // this function will panic if the "unbound names" invariant is violated
        Ok(Self::create(
            rr.if_all.iter().map(to_human).collect(),
            rr.then.iter().map(to_human).collect(),
        )
        .expect("Reasoner rule was invalid."))
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
    UnboundImplied(String),
}

#[derive(Debug, Eq, PartialEq)]
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

fn iter_local_reasoner_entities<'a>(res: &'a [reasoner::Triple]) -> impl Iterator<Item = u32> + 'a {
    res.iter().flat_map(|trip| {
        once(trip.subject.0)
            .chain(once(trip.property.0))
            .chain(once(trip.object.0))
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
    fn to_reasoners_rule_no_translation() {
        let trans = Translator::<&str>::from_iter(vec![]);

        let r = Rule::<&str>::create(
            vec![Restriction {
                subject: Entity::Any("a".into()),
                property: Entity::Exactly("unknown_entity"),
                object: Entity::Any("b".into()),
            }],
            vec![],
        )
        .unwrap();
        let err = r.to_reasoners_rule(&trans).unwrap_err();
        assert_eq!(err, NoTranslation(&"unknown_entity"));

        let r = Rule::<&str>::create(
            vec![],
            vec![Restriction {
                subject: Entity::Exactly("unknown_entity"),
                property: Entity::Exactly("unknown_entity"),
                object: Entity::Exactly("unknown_entity"),
            }],
        )
        .unwrap();
        let err = r.to_reasoners_rule(&trans).unwrap_err();
        assert_eq!(err, NoTranslation(&"unknown_entity"));
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

        let mut human_names = (0..).map(|a| format!("a{}", a));
        let mut next_name = || human_names.next().unwrap();
        let rule = Rule::from_reasoners_rule(&rr, &trans, &mut next_name).unwrap();
        assert_eq!(
            rule,
            Rule::<String> {
                if_all: [
                    Restriction {
                        subject: Entity::Any("a0".into()),
                        property: Entity::Exactly("ancestor".into()),
                        object: Entity::Any("a1".into()),
                    },
                    Restriction {
                        subject: Entity::Any("a1".into()),
                        property: Entity::Exactly("ancestor".into()),
                        object: Entity::Any("a2".into()),
                    },
                ]
                .to_vec(),
                then: [Restriction {
                    subject: Entity::Any("a0".into()),
                    property: Entity::Exactly("ancestor".into()),
                    object: Entity::Any("a2".into()),
                }]
                .to_vec(),
            }
        );
    }

    #[test]
    fn to_from_reasoners_rule() {
        let trans = Translator::<String>::from_iter(vec!["ancestor".into()]);
        let original = Rule::<String> {
            if_all: [
                Restriction {
                    subject: Entity::Any("a0".into()),
                    property: Entity::Exactly("ancestor".into()),
                    object: Entity::Any("a1".into()),
                },
                Restriction {
                    subject: Entity::Any("a1".into()),
                    property: Entity::Exactly("ancestor".into()),
                    object: Entity::Any("a2".into()),
                },
            ]
            .to_vec(),
            then: [Restriction {
                subject: Entity::Any("a0".into()),
                property: Entity::Exactly("ancestor".into()),
                object: Entity::Any("a2".into()),
            }]
            .to_vec(),
        };
        let rr = original.to_reasoners_rule(&trans).unwrap();
        let mut human_names = (0..).map(|a| format!("a{}", a));
        let mut next_name = || human_names.next().unwrap();
        let end = Rule::from_reasoners_rule(&rr, &trans, &mut next_name).unwrap();
        assert_eq!(original, end);
    }

    #[test]
    fn create_invalid() {
        Rule::<usize>::create(
            [].to_vec(),
            [Restriction {
                subject: Entity::Any("a".into()),
                property: Entity::Any("a".into()),
                object: Entity::Any("a".into()),
            }]
            .to_vec(),
        )
        .unwrap_err();
    }
}
