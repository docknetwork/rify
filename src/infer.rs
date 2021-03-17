use crate::common::back;
use crate::common::{forward, vertices};
use crate::reasoner::{Quad, Reasoner};
use crate::rule::{LowRule, Rule};
use crate::translator::Translator;
use alloc::collections::BTreeSet;

/// Make all possible inferences.
pub fn infer<Unbound: Ord + Clone, Bound: Ord + Clone>(
    premises: &[[Bound; 4]],
    rules: &[Rule<Unbound, Bound>],
) -> Vec<[Bound; 4]> {
    let tran: Translator<Bound> = vertices(premises, rules).cloned().collect();
    let lpremises: Vec<Quad> = premises
        .iter()
        .map(|quad| forward(&tran, quad).unwrap())
        .collect();
    let lrules: Vec<LowRule> = rules
        .iter()
        .map(|rule| rule.lower(&tran).map_err(|_| ()).unwrap())
        .collect();
    low_infer(&lpremises, &lrules)
        .into_iter()
        .map(|quad| clones(back(&tran, quad).unwrap()))
        .collect()
}

/// A version of infer that operates on lowered input an returns output in lowered form.
fn low_infer(premises: &[Quad], rules: &[LowRule]) -> Vec<Quad> {
    let mut rs = Reasoner::default();
    for prem in premises {
        rs.insert(prem.clone());
    }
    let initial_len = rs.claims_ref().len(); // number of premises after dedup
    debug_assert!(initial_len <= premises.len());

    loop {
        let mut to_add = BTreeSet::<Quad>::new();
        for rr in rules.iter() {
            rs.apply(&mut rr.if_all.clone(), &mut rr.inst.clone(), &mut |inst| {
                let ins = inst.as_ref();
                for implied in &rr.then {
                    let new_quad = [
                        ins[&implied.s.0],
                        ins[&implied.p.0],
                        ins[&implied.o.0],
                        ins[&implied.g.0],
                    ]
                    .into();
                    if !rs.contains(&new_quad) {
                        to_add.insert(new_quad);
                    }
                }
            });
        }
        if to_add.is_empty() {
            break;
        }
        for new in to_add.into_iter() {
            rs.insert(new);
        }
    }

    // remove all premises, we only want to return new inferences
    let mut claims = rs.claims();
    drop(claims.drain(0..initial_len));

    claims
}

fn clones<T: Clone>(arr: [&T; 4]) -> [T; 4] {
    let [a, b, c, d] = arr;
    [a.clone(), b.clone(), c.clone(), d.clone()]
}
