extern crate alloc;
extern crate core;

mod common;
pub mod mapstack;
pub mod reasoner;
pub mod rule;
#[cfg(test)]
mod test;
pub mod translator;
pub mod vecset;

use crate::reasoner::{Triple, TripleStore};
use crate::rule::{ReasonersRule, Rule};
use crate::translator::Translator;
use alloc::collections::{BTreeMap, BTreeSet};

pub fn prove<'a, T: Ord>(
    premises: &'a [[T; 3]],
    to_prove: &'a [[T; 3]],
    rules: &'a [Rule<&T>],
) -> Result<Vec<Ponens<&'a T>>, CantProve> {
    let tran: Translator<&T> = rules
        .iter()
        .flat_map(|rule| rule.all_bound_entities().cloned())
        .chain(premises.iter().flatten())
        .collect();

    let as_raw = |[s, p, o]: &[T; 3]| -> Triple {
        Triple::from_tuple(
            tran.forward(&s).unwrap(),
            tran.forward(&p).unwrap(),
            tran.forward(&o).unwrap(),
        )
    };

    if to_prove
        .iter()
        .flatten()
        .any(|t| tran.forward(&t).is_none())
    {
        return Err(CantProve::Unprovable);
    }
    let to_prove_raw: Vec<Triple> = to_prove.iter().map(as_raw).collect();

    let mut ts = TripleStore::new();
    for spo in premises {
        ts.insert(as_raw(spo));
    }

    // reasoner_rules
    let mut rrs: Vec<ReasonersRule> = rules
        .iter()
        .map(|r| r.to_reasoners_rule(&tran).map_err(|_| ()).unwrap())
        .collect();

    // statement (Triple) is proved by applying step (ReasonersProofStep)
    let mut arguments: BTreeMap<Triple, ReasonersProofStep> = BTreeMap::new();

    // reason
    loop {
        if to_prove_raw.iter().all(|tp| ts.contains(tp)) {
            break;
        }
        let mut to_add = BTreeSet::<Triple>::new();
        for (index, rule) in rrs.iter_mut().enumerate() {
            let mut if_all = &mut rule.if_all;
            let mut inst = &mut rule.inst;
            let then = &rule.then;
            ts.apply(&mut if_all, &mut inst, &mut |inst| {
                let ins = inst.as_ref();
                for implied in then {
                    let new_triple = Triple::from_tuple(
                        ins[&implied.subject.0],
                        ins[&implied.property.0],
                        ins[&implied.object.0],
                    );
                    if !ts.contains(&new_triple) {
                        arguments
                            .entry(new_triple.clone())
                            .or_insert_with(|| ReasonersProofStep {
                                rule_index: index,
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

    if !to_prove_raw.iter().all(|tp| ts.contains(tp)) {
        return Err(CantProve::Unprovable);
    }

    let mut raw_proof: Vec<ReasonersProofStep> = Vec::new();
    todo!("populate raw_proof, recursivly pulling instations from 'arguments' map");
}

pub enum CantProve {
    /// Entire search space was exhausted
    Unprovable,
}

pub struct Ponens<T> {
    pub rule: Rule<T>,
    pub instantiation: Vec<T>,
    pub therefore: [T; 3],
}

struct ReasonersProofStep {
    rule_index: usize,
    instantiations: BTreeMap<u32, u32>,
}

#[derive(Debug)]
struct NoTranslation;
