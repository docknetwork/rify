#![cfg(test)]
#![feature(test)]

extern crate test;

use core::fmt::Debug;
use rify::Entity::{Bound as B, Unbound as U};
use rify::*;
use test::Bencher;

const DG: &str = "default_graph";

mod ancestry {
    use super::*;
    const PARENT: &str = "parent";
    const ANCESTOR: &str = "ancestor";

    fn rules() -> Vec<rify::Rule<&'static str, &'static str>> {
        decl_rules(&[
            [
                &[[U("a"), B(PARENT), U("b"), B(DG)]],
                &[[U("a"), B(ANCESTOR), U("b"), B(DG)]],
            ],
            [
                &[
                    [U("a"), B(ANCESTOR), U("b"), B(DG)],
                    [U("b"), B(ANCESTOR), U("c"), B(DG)],
                ],
                &[[U("a"), B(ANCESTOR), U("c"), B(DG)]],
            ],
        ])
    }

    // Contains intentional leak; don't use outside of tests.
    fn facts(numnodes: usize) -> Vec<[&'static str; 4]> {
        let nodes: Vec<&str> = (0..numnodes)
            .map(|n| Box::leak(format!("node_{}", n).into_boxed_str()) as &str)
            .collect();
        let facts: Vec<[&str; 4]> = nodes
            .iter()
            .zip(nodes.iter().cycle().skip(1))
            .map(|(a, b)| [a, PARENT, b, DG])
            .collect();
        facts
    }

    #[bench]
    fn infer_(b: &mut Bencher) {
        let facts = facts(20);
        let rules = rules();
        b.iter(|| infer(&facts, &rules));
    }

    #[bench]
    fn prove_(b: &mut Bencher) {
        let facts = facts(20);
        let rules = rules();
        b.iter(|| prove(&facts, &[[PARENT, PARENT, PARENT, PARENT]], &rules).unwrap_err());
    }

    #[bench]
    fn infer_30(b: &mut Bencher) {
        let facts = facts(30);
        let rules = rules();
        b.iter(|| infer(&facts, &rules));
    }

    #[bench]
    fn prove_30(b: &mut Bencher) {
        let facts = facts(30);
        let rules = rules();
        b.iter(|| prove(&facts, &[[PARENT, PARENT, PARENT, PARENT]], &rules).unwrap_err());
    }
}

mod recursion_minimal {
    use super::*;

    const RULES: &[[&[[rify::Entity<&str, &str>; 4]]; 2]] = &[
        [
            &[
                [B("andrew"), B("claims"), U("c"), B(DG)],
                [U("c"), B("subject"), U("s"), B(DG)],
                [U("c"), B("property"), U("p"), B(DG)],
                [U("c"), B("object"), U("o"), B(DG)],
            ],
            &[[U("s"), U("p"), U("o"), B(DG)]],
        ],
        [
            &[
                [U("person_a"), B("is"), B("awesome"), B(DG)],
                [U("person_a"), B("friendswith"), U("person_b"), B(DG)],
            ],
            &[[U("person_b"), B("is"), B("awesome"), B(DG)]],
        ],
        [
            &[[U("person_a"), B("friendswith"), U("person_b"), B(DG)]],
            &[[U("person_b"), B("friendswith"), U("person_a"), B(DG)]],
        ],
    ];

    const FACTS: &[[&str; 4]] = &[
        ["soyoung", "friendswith", "nick", DG],
        ["nick", "friendswith", "elina", DG],
        ["elina", "friendswith", "sam", DG],
        ["sam", "friendswith", "fausto", DG],
        ["fausto", "friendswith", "lovesh", DG],
        ["andrew", "claims", "_:claim1", DG],
        ["_:claim1", "subject", "lovesh", DG],
        ["_:claim1", "property", "is", DG],
        ["_:claim1", "object", "awesome", DG],
    ];

    #[bench]
    fn infer_(b: &mut Bencher) {
        let rules = decl_rules(RULES);
        b.iter(|| infer(FACTS, &rules));
    }

    #[bench]
    fn prove_(b: &mut Bencher) {
        let rules = decl_rules(RULES);
        let composite_claims: &[[&str; 4]] = &[
            ["soyoung", "is", "awesome", "default_graph"],
            ["nick", "is", "awesome", "default_graph"],
        ];
        b.iter(|| prove(FACTS, composite_claims, &rules));
    }
}

pub fn decl_rules<Unbound: Ord + Debug + Clone, Bound: Ord + Clone>(
    rs: &[[&[[rify::Entity<Unbound, Bound>; 4]]; 2]],
) -> Vec<rify::Rule<Unbound, Bound>> {
    rs.iter()
        .map(|[ifa, then]| rify::Rule::create(ifa.to_vec(), then.to_vec()).unwrap())
        .collect()
}
