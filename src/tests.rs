use crate::common::{any, exa};
use crate::reasoner::{Triple, TripleStore};
use crate::rule::{Entity, ReasonersRule, Rule};
use crate::translator::Translator;
use alloc::collections::BTreeSet;
use core::iter::once;

#[test]
fn ancestry() {
    // load data
    let parent = "parent";
    let ancestor = "ancestor";
    let nodes: Vec<_> = (0..10).map(|a| format!("n{}", a)).collect();

    // create a translator to map human readable names to u32
    let tran: Translator<&str> = nodes
        .iter()
        .map(AsRef::as_ref)
        .chain(once(parent))
        .chain(once(ancestor))
        .collect();

    // load rules
    let rules: &[[&[[Entity<&str, &str>; 3]]; 2]] = &[
        [
            &[[any("a"), exa(&parent), any("b")]],
            &[[any("a"), exa(&ancestor), any("b")]],
        ],
        [
            &[
                [any("a"), exa(&ancestor), any("b")],
                [any("b"), exa(&ancestor), any("c")],
            ],
            &[[any("a"), exa(&ancestor), any("c")]],
        ],
    ];
    let mut rrs: Vec<ReasonersRule> = rules
        .iter()
        .map(|rule| reasoner_rule(*rule, &tran))
        .collect();

    // load data into reasoner
    let mut ts = TripleStore::new();
    // initial facts: (n_a parent n_a+1), (n_last parent n_0)
    let initial_claims: Vec<(&str, &str, &str)> = nodes
        .iter()
        .zip(nodes.iter().cycle().skip(1))
        .map(|(a, b)| (a.as_str(), parent, b.as_str()))
        .collect();
    for (s, p, o) in &initial_claims {
        ts.insert(Triple::from_tuple(
            tran.forward(s).unwrap(),
            tran.forward(p).unwrap(),
            tran.forward(o).unwrap(),
        ));
    }

    // reason
    loop {
        let mut to_add = BTreeSet::<Triple>::new();
        for rule in rrs.iter_mut() {
            let mut if_all = &mut rule.if_all;
            let mut inst = &mut rule.inst;
            let then = &rule.then;
            ts.apply(&mut if_all, &mut inst, &mut |inst| {
                for implied in then {
                    let inst = inst.as_ref();
                    let new_triple = Triple::from_tuple(
                        inst[&implied.subject.0],
                        inst[&implied.property.0],
                        inst[&implied.object.0],
                    );
                    if !ts.contains(&new_triple) {
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

    // convert results back to human readable tuples
    let claims: BTreeSet<(&str, &str, &str)> = ts
        .claims()
        .iter()
        .map(|triple| {
            (
                *tran.back(triple.subject.0).unwrap(),
                *tran.back(triple.property.0).unwrap(),
                *tran.back(triple.object.0).unwrap(),
            )
        })
        .collect();

    // assert results
    let expected_claims: BTreeSet<(&str, &str, &str)> = initial_claims
        .iter()
        .cloned()
        .chain(nodes.iter().flat_map(|a| {
            nodes
                .iter()
                .map(move |b| (a.as_str(), ancestor, b.as_str()))
        }))
        .collect();
    assert_eq!(claims, expected_claims);
}

/// panics if an unbound name is implied
/// pancis if rule contains bound names that are not present in Translator
fn reasoner_rule(rule: [&[[Entity<&str, &str>; 3]]; 2], trans: &Translator<&str>) -> ReasonersRule {
    let [if_all, then] = rule;
    Rule::<&str, &str>::create(if_all, then)
        .unwrap()
        .to_reasoners_rule(trans)
        .unwrap()
}
