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

    debug_assert!(
        {
            let mut rc = claims.clone();
            rc.sort_unstable();
            rc.dedup();
            rc.len() == claims.len()
        },
        "duplicate inferences should never be reported, this is a bug in rify"
    );
    debug_assert!(
        {
            let rc = claims.iter().collect::<BTreeSet<_>>();
            premises.iter().all(|p| !rc.contains(p))
        },
        "premises should never be reported as new inferences, this is a bug in rify"
    );

    claims
}

fn clones<T: Clone>(arr: [&T; 4]) -> [T; 4] {
    let [a, b, c, d] = arr;
    [a.clone(), b.clone(), c.clone(), d.clone()]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::decl_rules;
    use crate::rule::Entity::{Bound as B, Unbound as U};

    #[test]
    fn ancestry() {
        let parent = "parent";
        let ancestor = "ancestor";
        let default_graph = "default_graph";
        let nodes: Vec<String> = (0..10).map(|n| format!("node_{}", n)).collect();
        let facts: Vec<[&str; 4]> = nodes
            .iter()
            .zip(nodes.iter().cycle().skip(1))
            .map(|(a, b)| [a, parent, b, default_graph])
            .collect();
        let rules = decl_rules(&[
            [
                &[[U("a"), B(parent), U("b"), B(default_graph)]],
                &[[U("a"), B(ancestor), U("b"), B(default_graph)]],
            ],
            [
                &[
                    [U("a"), B(ancestor), U("b"), B(default_graph)],
                    [U("b"), B(ancestor), U("c"), B(default_graph)],
                ],
                &[[U("a"), B(ancestor), U("c"), B(default_graph)]],
            ],
        ]);
        let mut inferences = infer(&facts, &rules);
        // every node is ancestor to every other node
        let mut expected: Vec<[&str; 4]> = nodes
            .iter()
            .flat_map(|n0| nodes.iter().map(move |n1| (n0, n1)))
            .map(|(n0, n1)| [n0, ancestor, n1, default_graph])
            .collect();

        {
            // checking multiset equality
            expected.sort();
            inferences.sort();
            assert_eq!(inferences, expected);
        }
    }

    #[test]
    fn unconditional_rule() {
        let facts: Vec<[&str; 4]> = vec![];
        let rules = decl_rules::<&str, &str>(&[[
            &[],
            &[[B("nachos"), B("are"), B("food"), B("default_graph")]],
        ]]);
        let inferences = infer::<&str, &str>(&facts, &rules);
        assert_eq!(&inferences, &[["nachos", "are", "food", "default_graph"]]);
    }

    #[test]
    fn reasoning_is_already_complete() {
        let facts: Vec<[&str; 4]> = vec![
            ["nachos", "are", "tasty", "default_graph"],
            ["nachos", "are", "food", "default_graph"],
        ];
        let rules = decl_rules::<&str, &str>(&[[
            &[[B("nachos"), B("are"), B("tasty"), B("default_graph")]],
            &[[B("nachos"), B("are"), B("food"), B("default_graph")]],
        ]]);
        let expected: [[&str; 4]; 0] = [];
        assert_eq!(&infer(&facts, &rules), &expected)
    }

    #[test]
    fn empty_ruleset() {
        let facts: Vec<[&str; 4]> = vec![
            ["nachos", "are", "tasty", "default_graph"],
            ["nachos", "are", "food", "default_graph"],
        ];
        let rules = decl_rules::<&str, &str>(&[]);
        let inferences = infer::<&str, &str>(&facts, &rules);
        let expected: [[&str; 4]; 0] = [];
        assert_eq!(&inferences, &expected);
    }

    #[test]
    fn empty_claimgraph() {
        let facts: Vec<[&str; 4]> = vec![];
        let rules = decl_rules::<&str, &str>(&[[
            &[[B("nachos"), B("are"), B("tasty"), B("default_graph")]],
            &[[B("nachos"), B("are"), B("food"), B("default_graph")]],
        ]]);
        let inferences = infer::<&str, &str>(&facts, &rules);
        let expected: [[&str; 4]; 0] = [];
        assert_eq!(&inferences, &expected);
    }
}
