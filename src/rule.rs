//! The reasoner's rule representation is optimized machine use, not human use. Reading and writing
//! rules directly is difficult for humans. This module provides a human friendly rule description
//! datatype that can be lowered to the reasoner's rule representation.

use crate::reasoner;
use crate::translator::Translator;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::iter::once;
use core::ops::Not;

pub struct ReasonersRule {
    pub if_all: Vec<reasoner::Triple>,
    pub then: Vec<reasoner::Triple>,
    pub inst: reasoner::Instantiations,
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub enum Entity {
    Any(String),
    Exactly(String),
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct Restriction {
    pub subject: Entity,
    pub property: Entity,
    pub object: Entity,
}

pub struct Rule {
    if_all: Vec<Restriction>,
    then: Vec<Restriction>,
}

impl Rule {
    pub fn create(if_all: Vec<Restriction>, then: Vec<Restriction>) -> Result<Rule, InvalidRule> {
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
        tran: &Translator<String>,
    ) -> Result<ReasonersRule, NoTranslation> {
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
        let bound_map: BTreeMap<&String, u32> = iter_entities(&self.if_all)
            .filter_map(as_bound)
            .map(|s| (s, inc(&mut next_local)))
            .collect();

        // gets the local name for an human named entity
        let local_name = |entity: &Entity| -> u32 {
            match entity {
                Entity::Any(s) => unbound_map[s],
                Entity::Exactly(s) => bound_map[s],
            }
        };
        // converts a human readable restriction list to a locally scoped requirement list
        let to_requirements = |rest: &[Restriction]| -> Vec<reasoner::Triple> {
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
                    let global_name = tran.forward(human_name).ok_or(NoTranslation)?;
                    Ok((*local_name, global_name))
                })
                .collect::<Result<_, _>>()?,
        })
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
pub struct NoTranslation;

fn as_unbound(e: &Entity) -> Option<&String> {
    match e {
        Entity::Any(s) => Some(s),
        Entity::Exactly(_) => None,
    }
}

fn as_bound(e: &Entity) -> Option<&String> {
    match e {
        Entity::Any(_) => None,
        Entity::Exactly(s) => Some(s),
    }
}

fn iter_entities(res: &[Restriction]) -> impl Iterator<Item = &Entity> {
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
    #[test]
    fn similar_names() {
        // test rule
        // (?a <a> <b>) ->
        // ?a should be a separate entity than <a>

        // convert the rule to a reasonersrule and somhow make sure ?a != <a>
    }

    #[test]
    fn to_reasoners_rule() {}

    #[test]
    fn from_reasoners_rule() {}

    #[test]
    fn to_from_reasoners_rule() {}
}
