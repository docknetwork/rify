extern crate alloc;
extern crate core;

mod common;
pub mod mapstack;
pub mod reasoner;
pub mod rule;
#[cfg(test)]
mod tests;
pub mod translator;
pub mod vecset;

use crate::reasoner::{Triple, TripleStore};
use crate::rule::{Entity, ReasonersRule, Rule};
use crate::translator::Translator;
use alloc::collections::{BTreeMap, BTreeSet};

pub fn prove<'a, Unbound: Ord, Bound: Ord + Clone>(
    premises: &'a [[Bound; 3]],
    to_prove: &'a [[Bound; 3]],
    rules: &'a [&'a Rule<'a, Unbound, Bound>],
) -> Result<Vec<RuleApplication<'a, Unbound, Bound>>, CantProve> {
    let tran: Translator<Bound> = rules
        .iter()
        .flat_map(|rule| rule.iter_entities().filter_map(Entity::as_bound))
        .chain(premises.iter().flatten())
        .cloned()
        .collect();
    let as_raw = |[s, p, o]: &[Bound; 3]| -> Option<Triple> {
        Some(Triple::from_tuple(
            tran.forward(&s)?,
            tran.forward(&p)?,
            tran.forward(&o)?,
        ))
    };
    let rpremises: Vec<Triple> = premises.iter().map(|spo| as_raw(spo).unwrap()).collect();
    let rto_prove: Vec<Triple> = to_prove
        .iter()
        .map(as_raw)
        .collect::<Option<_>>()
        .ok_or(CantProve::NovelName)?;
    let rrules: Vec<ReasonersRule> = rules
        .iter()
        .cloned()
        .map(|rule: &Rule<'a, Unbound, Bound>| -> ReasonersRule {
            rule.to_reasoners_rule(&tran).map_err(|_| ()).unwrap()
        })
        .collect();

    let rproof = raw_prove(&rpremises, &rto_prove, &rrules)?;

    // convert to proof
    Ok(rproof
        .iter()
        .map(|_rra: &RawRuleApplication| -> RuleApplication<Unbound, Bound> { unimplemented!() })
        .collect())
}

fn raw_prove<'a>(
    premises: &'a [Triple],
    to_prove: &'a [Triple],
    rules: &'a [ReasonersRule],
) -> Result<Vec<RawRuleApplication<'a>>, CantProve> {
    let mut ts = TripleStore::new();
    for prem in premises {
        ts.insert(prem.clone());
    }

    // statement (Triple) is proved by applying step (ReasonersProofStep)
    let mut arguments: BTreeMap<Triple, RawRuleApplication> = BTreeMap::new();

    // reason
    loop {
        if to_prove.iter().all(|tp| ts.contains(tp)) {
            break;
        }
        let mut to_add = BTreeSet::<Triple>::new();
        for rr in rules {
            ts.apply(&mut rr.if_all.clone(), &mut rr.inst.clone(), &mut |inst| {
                let ins = inst.as_ref();
                for implied in &rr.then {
                    let new_triple = Triple::from_tuple(
                        ins[&implied.subject.0],
                        ins[&implied.property.0],
                        ins[&implied.object.0],
                    );
                    if !ts.contains(&new_triple) {
                        arguments
                            .entry(new_triple.clone())
                            .or_insert_with(|| RawRuleApplication {
                                rule: rr,
                                instantiations: ins.clone(),
                            });
                        to_add.insert(new_triple);
                    }
                }
            });
        }
        if to_add.is_empty() {
            break;
        }
        for new in to_add.into_iter() {
            ts.insert(new);
        }
    }

    if !to_prove.iter().all(|tp| ts.contains(tp)) {
        return Err(CantProve::ExaustedSearchSpace);
    }

    let mut ret: Vec<RawRuleApplication> = Vec::new();
    for claim in to_prove {
        recall_proof(claim, &arguments, &mut ret);
    }
    Ok(ret)
}

/// TODO, this fuction is not tail recursive
fn recall_proof<'a>(
    // globally scoped triple to prove
    to_prove: &Triple,
    arguments: &BTreeMap<Triple, RawRuleApplication<'a>>,
    outp: &mut Vec<RawRuleApplication<'a>>,
) {
    let to_global_scope = |rra: &RawRuleApplication, locally_scoped_entity: u32| -> u32 {
        let concrete = rra.rule.inst.as_ref().get(&locally_scoped_entity);
        let found = rra.instantiations.get(&locally_scoped_entity);
        debug_assert!(if let (Some(c), Some(f)) = (concrete, found) {
            c == f
        } else {
            true
        });
        *concrete.or(found).unwrap()
    };

    if let Some(application) = arguments.get(to_prove) {
        // for every required sub-statement, recurse
        for triple in &application.rule.if_all {
            recall_proof(
                &Triple::from_tuple(
                    to_global_scope(application, triple.subject.0),
                    to_global_scope(application, triple.property.0),
                    to_global_scope(application, triple.object.0),
                ),
                arguments,
                outp,
            );
        }
        // push the application onto output and return
        outp.push(application.clone());
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum CantProve {
    /// Entire search space was exhausted. The requested proof does not exists.
    ExaustedSearchSpace,
    /// One of the entities in to_prove was never mentioned in the provided premises or
    /// rules. The requested proof does not exists.
    NovelName,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RawRuleApplication<'a> {
    rule: &'a ReasonersRule,
    instantiations: BTreeMap<u32, u32>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct RuleApplication<'a, Unbound, Bound> {
    rule: &'a Rule<'a, Unbound, Bound>,
    instantiations: BTreeMap<Unbound, Bound>,
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::rule::Entity::{Any, Exactly as Exa};

    #[test]
    fn novel_name() {
        assert_eq!(
            prove::<&str, &str>(&[], &[["andrew", "score", "awesome"]], &[]).unwrap_err(),
            CantProve::NovelName
        );
    }

    #[test]
    fn prove_already_stated() {
        assert_eq!(
            prove::<&str, &str>(
                &[["doggo", "score", "11"]],
                &[["doggo", "score", "11"]],
                &[]
            )
            .unwrap(),
            Vec::new()
        );
    }

    #[test]
    fn prove_() {
        let awesome_score_axiom = Rule::create(
            &[
                [Any("boi"), Exa("is"), Exa("awesome")], // if someone is awesome
                [Any("boi"), Exa("score"), Any("s")],    // and they have some score
            ],
            &[[Any("boi"), Exa("score"), Exa("awesome")]], // then they must have an awesome score
        )
        .unwrap();
        assert_eq!(
            prove::<&str, &str>(
                &[["you", "score", "unspecified"], ["you", "is", "awesome"]],
                &[["you", "score", "awesome"]],
                &[&awesome_score_axiom]
            )
            .unwrap(),
            vec![RuleApplication {
                rule: &awesome_score_axiom,
                instantiations: [("boi", "you"), ("s", "unspecified")]
                    .iter()
                    .cloned()
                    .collect()
            }]
        );
    }
}
