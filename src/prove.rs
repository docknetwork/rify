use crate::common::forward;
use crate::common::vertices;
use crate::common::LowRuleApplication;
use crate::reasoner::{Quad, Reasoner};
use crate::rule::{Entity, LowRule, Rule};
use crate::translator::Translator;
use alloc::collections::{BTreeMap, BTreeSet};
use core::fmt::{Debug, Display};

/// Locate a proof of some composite claims given the provied premises and rules.
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use rify::{
///     prove,
///     Entity::{Unbound, Bound},
///     Rule, RuleApplication,
/// };
///
/// // (?a, is, awesome) ∧ (?a, score, ?s) -> (?a score, awesome)
/// let awesome_score_axiom = Rule::create(
///     vec![
///         // if someone is awesome
///         [Unbound("a"), Bound("is"), Bound("awesome"), Bound("default_graph")],
///         // and they have some score
///         [Unbound("a"), Bound("score"), Unbound("s"), Bound("default_graph")],
///     ],
///     vec![
///         // then they must have an awesome score
///         [Unbound("a"), Bound("score"), Bound("awesome"), Bound("default_graph")]
///     ],
/// )?;
///
/// assert_eq!(
///     prove::<&str, &str>(
///         // list of already known facts (premises)
///         &[
///             ["you", "score", "unspecified", "default_graph"],
///             ["you", "is", "awesome", "default_graph"]
///         ],
///         // the thing we want to prove
///         &[["you", "score", "awesome", "default_graph"]],
///         // ordered list of logical rules
///         &[awesome_score_axiom]
///     )?,
///     &[
///         // the desired statement is be proven by instatiating the `awesome_score_axiom`
///         // (you is awesome) ∧ (you score unspecified) -> (you score awesome)
///         RuleApplication {
///             rule_index: 0,
///             instantiations: vec!["you", "unspecified"]
///         }
///     ]
/// );
/// # Ok(())
/// # }
/// ```
pub fn prove<'a, Unbound: Ord + Clone, Bound: Ord + Clone>(
    premises: &'a [[Bound; 4]],
    to_prove: &'a [[Bound; 4]],
    rules: &'a [Rule<Unbound, Bound>],
) -> Result<Vec<RuleApplication<Bound>>, CantProve> {
    let tran: Translator<Bound> = vertices(premises, rules).cloned().collect();
    let lpremises: Vec<Quad> = premises
        .iter()
        .map(|spog| forward(&tran, spog).unwrap())
        .collect();
    let lto_prove: Vec<Quad> = to_prove
        .iter()
        .map(|spog| forward(&tran, spog))
        .collect::<Option<_>>()
        .ok_or(CantProve::NovelName)?;
    let lrules: Vec<LowRule> = rules
        .iter()
        .cloned()
        .map(|rule: Rule<Unbound, Bound>| -> LowRule { rule.lower(&tran).map_err(|_| ()).unwrap() })
        .collect();

    let lproof = low_prove(&lpremises, &lto_prove, &lrules)?;

    // convert to proof
    Ok(lproof
        .iter()
        .map(|rra: &LowRuleApplication| -> RuleApplication<Bound> {
            rra.raise(&rules[rra.rule_index], &tran)
        })
        .collect())
}

fn low_prove(
    premises: &[Quad],
    to_prove: &[Quad],
    rules: &[LowRule],
) -> Result<Vec<LowRuleApplication>, CantProve> {
    let mut rs = Reasoner::default();
    for prem in premises {
        rs.insert(prem.clone());
    }

    // statement (Quad) is proved by applying rule (LowRuleApplication)
    let mut arguments: BTreeMap<Quad, LowRuleApplication> = BTreeMap::new();

    // reason
    loop {
        if to_prove.iter().all(|tp| rs.contains(tp)) {
            break;
        }
        let mut to_add = BTreeSet::<Quad>::new();
        for (rule_index, rr) in rules.iter().enumerate() {
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
                        arguments
                            .entry(new_quad.clone())
                            .or_insert_with(|| LowRuleApplication {
                                rule_index,
                                instantiations: ins.clone(),
                            });
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

    if !to_prove.iter().all(|tp| rs.contains(tp)) {
        return Err(CantProve::ExhaustedSearchSpace);
    }

    let mut ret: Vec<LowRuleApplication> = Vec::new();
    for claim in to_prove {
        recall_proof(claim, &mut arguments, rules, &mut ret);
    }
    Ok(ret)
}

// this function is not tail recursive
/// As this function populates the output. It removes corresponding arguments from the input.
/// The reason being that a single argument does not need to be proved twice. Once is is
/// proved, it can be treated as a premise.
fn recall_proof(
    // the globally scoped quad for which to find arguments
    to_prove: &Quad,
    arguments: &mut BTreeMap<Quad, LowRuleApplication>,
    rules: &[LowRule],
    outp: &mut Vec<LowRuleApplication>,
) {
    let to_global_scope = |rra: &LowRuleApplication, locally_scoped: usize| -> usize {
        let concrete = rules[rra.rule_index].inst.as_ref().get(&locally_scoped);
        let found = rra.instantiations.get(&locally_scoped);
        if let (Some(c), Some(f)) = (concrete, found) {
            debug_assert_eq!(c, f);
        }
        *concrete.or(found).unwrap()
    };

    if let Some(application) = arguments.remove(to_prove) {
        // for every required sub-statement, recurse
        for quad in &rules[application.rule_index].if_all {
            let Quad { s, p, o, g } = quad;
            recall_proof(
                &[
                    to_global_scope(&application, s.0),
                    to_global_scope(&application, p.0),
                    to_global_scope(&application, o.0),
                    to_global_scope(&application, g.0),
                ]
                .into(),
                arguments,
                rules,
                outp,
            );
        }
        // push the application onto output and return
        outp.push(application);
    }
}

#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
pub enum CantProve {
    /// Entire search space was exhausted. The requested proof does not exists.
    ExhaustedSearchSpace,
    /// One of the entities in to_prove was never mentioned in the provided premises or
    /// rules. The requested proof does not exists.
    NovelName,
}

impl Display for CantProve {
    fn fmt(&self, fmtr: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        Debug::fmt(self, fmtr)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for CantProve {}

#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
/// An element of a deductive proof. Proofs can be transmitted and later validatated as long as the
/// validator assumes the same rule list as the prover.
///
/// Unbound variables are bound to the values in `instanitations`. They are bound in order of
/// initial appearance.
///
/// Given the rule:
///
/// ```customlang
/// ifall
///   [?z ex:foo ?x DG]
/// then
///   [?x ex:bar ?z DG]
/// ```
///
/// and the RuleApplication:
///
/// ```customlang
/// RuleApplication {
///   rule_index: 0,
///   instantiations: vec!["foer", "bary"],
/// }
/// ```
///
/// The rule application represents the deductive proof:
///
/// ```customlang
/// [foer ex:foo bary DG]
/// therefore
/// [bary ex:bar foer DG]
/// ```
pub struct RuleApplication<Bound> {
    /// The index of the rule in the implicitly associated rule list.
    pub rule_index: usize,
    /// Bindings for unbound names in the rule in order of appearance.
    pub instantiations: Vec<Bound>,
}

impl<Bound: Clone> RuleApplication<Bound> {
    pub(crate) fn assumptions_when_applied<'a, Unbound: Ord + Clone>(
        &'a self,
        rule: &'a Rule<Unbound, Bound>,
    ) -> Result<impl Iterator<Item = [Bound; 4]> + 'a, BadRuleApplication> {
        self.bind_claims(rule, rule.if_all())
    }

    pub(crate) fn implications_when_applied<'a, Unbound: Ord + Clone>(
        &'a self,
        rule: &'a Rule<Unbound, Bound>,
    ) -> Result<impl Iterator<Item = [Bound; 4]> + 'a, BadRuleApplication> {
        self.bind_claims(rule, rule.then())
    }

    /// claims must be either if_all or then from rule
    fn bind_claims<'a, Unbound: Ord + Clone>(
        &'a self,
        rule: &'a Rule<Unbound, Bound>,
        claims: &'a [[Entity<Unbound, Bound>; 4]],
    ) -> Result<impl Iterator<Item = [Bound; 4]> + 'a, BadRuleApplication> {
        let cannon: BTreeMap<&Unbound, usize> = rule
            .cononical_unbound()
            .enumerate()
            .map(|(ub, n)| (n, ub))
            .collect();
        if cannon.len() != self.instantiations.len() {
            return Err(BadRuleApplication);
        }
        Ok(claims
            .iter()
            .cloned()
            .map(move |claim| bind_claim(claim, &cannon, &self.instantiations)))
    }
}

/// Panics
///
/// panics if an unbound entity is not registered in map
/// panics if the canonical index of unbound (according to map) is too large to index instanitations
fn bind_claim<Unbound: Ord, Bound: Clone>(
    [s, p, o, g]: [Entity<Unbound, Bound>; 4],
    map: &BTreeMap<&Unbound, usize>,
    instanitations: &[Bound],
) -> [Bound; 4] {
    [
        bind_entity(s, map, instanitations),
        bind_entity(p, map, instanitations),
        bind_entity(o, map, instanitations),
        bind_entity(g, map, instanitations),
    ]
}

/// Panics
///
/// panics if an unbound entity is not registered in map
/// panics if the canonical index of unbound (according to map) is too large to index instanitations
fn bind_entity<Unbound: Ord, Bound: Clone>(
    e: Entity<Unbound, Bound>,
    map: &BTreeMap<&Unbound, usize>,
    instanitations: &[Bound],
) -> Bound {
    match e {
        Entity::Unbound(a) => instanitations[map[&a]].clone(),
        Entity::Bound(e) => e,
    }
}

/// The Rule being applied expects a different number of name bindings.
#[derive(Debug)]
pub struct BadRuleApplication;

#[cfg(test)]
mod test {
    use super::*;
    use crate::common::decl_rules;
    use crate::common::inc;
    use crate::rule::Entity::{Bound as B, Unbound as U};
    use crate::validate::validate;
    use crate::validate::Valid;

    #[test]
    fn novel_name() {
        assert_eq!(
            prove::<&str, &str>(&[], &[["andrew", "score", "awesome", "default_graph"]], &[])
                .unwrap_err(),
            CantProve::NovelName
        );
    }

    #[test]
    fn search_space_exhausted() {
        let err = prove::<&str, &str>(
            &[
                ["score", "score", "score", "default_graph"],
                ["andrew", "andrew", "andrew", "default_graph"],
                ["awesome", "awesome", "awesome", "default_graph"],
            ],
            &[["andrew", "score", "awesome", "default_graph"]],
            &[],
        )
        .unwrap_err();
        assert_eq!(err, CantProve::ExhaustedSearchSpace);
        let err = prove::<&str, &str>(
            &[
                ["score", "score", "score", "default_graph"],
                ["andrew", "andrew", "andrew", "default_graph"],
                ["awesome", "awesome", "awesome", "default_graph"],
                ["backflip", "backflip", "backflip", "default_graph"],
                ["ability", "ability", "ability", "default_graph"],
            ],
            &[["andrew", "score", "awesome", "default_graph"]],
            &[
                Rule::create(vec![], vec![]).unwrap(),
                Rule::create(
                    vec![[U("a"), B("ability"), B("backflip"), U("g")]],
                    vec![[U("a"), B("score"), B("awesome"), U("g")]],
                )
                .unwrap(),
            ],
        )
        .unwrap_err();
        assert_eq!(err, CantProve::ExhaustedSearchSpace);
    }

    #[test]
    fn prove_already_stated() {
        assert_eq!(
            prove::<&str, &str>(
                &[["doggo", "score", "11", "default_graph"]],
                &[["doggo", "score", "11", "default_graph"]],
                &[]
            )
            .unwrap(),
            Vec::new()
        );
    }

    #[test]
    /// generate a single step proof
    fn prove_single_step() {
        // (?boi, is, awesome) ∧ (?boi, score, ?s) -> (?boi score, awesome)
        let awesome_score_axiom = Rule::create(
            vec![
                [U("boi"), B("is"), B("awesome"), U("g")], // if someone is awesome
                [U("boi"), B("score"), U("s"), U("g")],    // and they have some score
            ],
            vec![[U("boi"), B("score"), B("awesome"), U("g")]], // then they must have an awesome score
        )
        .unwrap();
        assert_eq!(
            prove::<&str, &str>(
                &[
                    ["you", "score", "unspecified", "default_graph"],
                    ["you", "is", "awesome", "default_graph"]
                ],
                &[["you", "score", "awesome", "default_graph"]],
                &[awesome_score_axiom]
            )
            .unwrap(),
            vec![
                // (you is awesome) ∧ (you score unspecified) -> (you score awesome)
                RuleApplication {
                    rule_index: 0,
                    instantiations: vec!["you", "default_graph", "unspecified"]
                }
            ]
        );
    }

    #[test]
    /// rules with a single unbound graphname cannot be applied accross graphnames
    fn graph_separation() {
        let awesome_score_axiom = Rule::create(
            vec![
                [U("boi"), B("is"), B("awesome"), U("g")],
                [U("boi"), B("score"), U("s"), U("g")],
            ],
            vec![[U("boi"), B("score"), B("awesome"), U("g")]],
        )
        .unwrap();

        prove::<&str, &str>(
            &[
                ["you", "score", "unspecified", "default_graph"],
                ["you", "is", "awesome", "default_graph"],
            ],
            &[["you", "score", "awesome", "default_graph"]],
            &[awesome_score_axiom.clone()],
        )
        .unwrap();
        assert_eq!(
            prove(
                &[
                    ["you", "score", "unspecified", "default_graph"],
                    ["you", "is", "awesome", "other_graph"]
                ],
                &[["you", "score", "awesome", "default_graph"]],
                &[awesome_score_axiom.clone()]
            )
            .unwrap_err(),
            CantProve::ExhaustedSearchSpace
        );
        assert_eq!(
            prove(
                &[
                    ["you", "score", "unspecified", "default_graph"],
                    ["you", "is", "awesome", "other_graph"]
                ],
                &[["you", "score", "awesome", "other_graph"]],
                &[awesome_score_axiom.clone()]
            )
            .unwrap_err(),
            CantProve::ExhaustedSearchSpace
        );
        assert_eq!(
            prove(
                &[
                    ["you", "score", "unspecified", "default_graph"],
                    ["you", "is", "awesome", "default_graph"],
                    // to prevent NovelName error:
                    ["other_graph", "other_graph", "other_graph", "other_graph"],
                ],
                &[["you", "score", "awesome", "other_graph"]],
                &[awesome_score_axiom.clone()]
            )
            .unwrap_err(),
            CantProve::ExhaustedSearchSpace
        );
    }

    #[test]
    fn prove_multi_step() {
        // Rules:
        // (andrew claims ?c) ∧ (?c subject ?s) ∧ (?c property ?p) ∧ (?c object ?o) -> (?s ?p ?o)
        // (?person_a is awesome) ∧ (?person_a friendswith ?person_b) -> (?person_b is awesome)
        // (?person_a friendswith ?person_b) -> (?person_b friendswith ?person_a)

        // Facts:
        // (soyoung friendswith nick)
        // (nick friendswith elina)
        // (elina friendswith sam)
        // (sam friendswith fausto)
        // (fausto friendswith lovesh)
        // (andrew claims _:claim1)
        // (_:claim1 subject lovesh)
        // (_:claim1 property is)
        // (_:claim1 object awesome)

        // Composite Claims:
        // (soyoung is awesome)
        // (nick is awesome)

        // the following rules operate only on the defualt graph
        let rules: Vec<Rule<&str, &str>> = {
            let ru: &[[&[[Entity<&str, &str>; 4]]; 2]] = &[
                [
                    &[
                        [B("andrew"), B("claims"), U("c"), B("default_graph")],
                        [U("c"), B("subject"), U("s"), B("default_graph")],
                        [U("c"), B("property"), U("p"), B("default_graph")],
                        [U("c"), B("object"), U("o"), B("default_graph")],
                    ],
                    &[[U("s"), U("p"), U("o"), B("default_graph")]],
                ],
                [
                    &[
                        [U("person_a"), B("is"), B("awesome"), B("default_graph")],
                        [
                            U("person_a"),
                            B("friendswith"),
                            U("person_b"),
                            B("default_graph"),
                        ],
                    ],
                    &[[U("person_b"), B("is"), B("awesome"), B("default_graph")]],
                ],
                [
                    &[[
                        U("person_a"),
                        B("friendswith"),
                        U("person_b"),
                        B("default_graph"),
                    ]],
                    &[[
                        U("person_b"),
                        B("friendswith"),
                        U("person_a"),
                        B("default_graph"),
                    ]],
                ],
            ];
            ru.iter()
                .map(|[ifa, then]| Rule::create(ifa.to_vec(), then.to_vec()).unwrap())
                .collect()
        };
        let facts: &[[&str; 4]] = &[
            ["soyoung", "friendswith", "nick", "default_graph"],
            ["nick", "friendswith", "elina", "default_graph"],
            ["elina", "friendswith", "sam", "default_graph"],
            ["sam", "friendswith", "fausto", "default_graph"],
            ["fausto", "friendswith", "lovesh", "default_graph"],
            ["andrew", "claims", "_:claim1", "default_graph"],
            ["_:claim1", "subject", "lovesh", "default_graph"],
            ["_:claim1", "property", "is", "default_graph"],
            ["_:claim1", "object", "awesome", "default_graph"],
        ];
        let composite_claims: &[[&str; 4]] = &[
            ["soyoung", "is", "awesome", "default_graph"],
            ["nick", "is", "awesome", "default_graph"],
        ];
        let expected_proof: Vec<RuleApplication<&str>> = {
            let ep: &[(usize, &[&str])] = &[
                (0, &["_:claim1", "lovesh", "is", "awesome"]),
                (2, &["fausto", "lovesh"]),
                (1, &["lovesh", "fausto"]),
                (2, &["sam", "fausto"]),
                (1, &["fausto", "sam"]),
                (2, &["elina", "sam"]),
                (1, &["sam", "elina"]),
                (2, &["nick", "elina"]),
                (1, &["elina", "nick"]),
                (2, &["soyoung", "nick"]),
                (1, &["nick", "soyoung"]),
            ];
            ep.iter()
                .map(|(rule_index, inst)| RuleApplication {
                    rule_index: *rule_index,
                    instantiations: inst.to_vec(),
                })
                .collect()
        };
        let proof = prove::<&str, &str>(facts, composite_claims, &rules).unwrap();
        assert!(
            proof.len() <= expected_proof.len(),
            "if this assertion fails, the generated proof length is longer than it was previously"
        );
        assert_eq!(
            proof, expected_proof,
            "if this assertion fails the proof may still be valid but the order of the proof may \
             have changed"
        );
        let Valid { assumed, implied } = validate(&rules, &proof).unwrap();
        for claim in composite_claims {
            assert!(implied.contains(claim));
            assert!(
                !facts.contains(claim),
                "all theorems are expected to be composite for this particular problem"
            );
        }
        for assumption in &assumed {
            assert!(
                assumed.contains(assumption),
                "This problem was expected to use all porvided assumptions."
            );
        }
    }

    #[test]
    fn ancestry_high_prove_and_verify() {
        let mut next_uniq = 0u32;
        let parent = inc(&mut next_uniq);
        let ancestor = inc(&mut next_uniq);
        let default_graph = inc(&mut next_uniq);
        let nodes: Vec<u32> = (0usize..10).map(|_| inc(&mut next_uniq)).collect();
        let facts: Vec<[u32; 4]> = nodes
            .iter()
            .zip(nodes.iter().cycle().skip(1))
            .map(|(a, b)| [*a, parent, *b, default_graph])
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
        let composite_claims = vec![
            [nodes[0], ancestor, *nodes.last().unwrap(), default_graph],
            [*nodes.last().unwrap(), ancestor, nodes[0], default_graph],
            [nodes[0], ancestor, nodes[0], default_graph],
            // (first node, parent, second node) is a premise
            [nodes[0], parent, nodes[1], default_graph],
        ];
        let proof = prove::<&str, u32>(&facts, &composite_claims, &rules).unwrap();
        let Valid { assumed, implied } = validate::<&str, u32>(&rules, &proof).unwrap();
        assert_eq!(
            &assumed,
            &facts.iter().cloned().collect(),
            "all supplied premises are expected to be used for this proof"
        );
        assert!(!facts.contains(&composite_claims[0]));
        assert!(!facts.contains(&composite_claims[1]));
        assert!(!facts.contains(&composite_claims[2]));
        assert!(facts.contains(&composite_claims[3]));
        for claim in composite_claims {
            assert!(implied.contains(&claim) ^ facts.contains(&claim));
        }
        for fact in facts {
            assert!(!implied.contains(&fact));
        }
    }

    #[test]
    fn no_proof_is_generated_for_facts() {
        let facts: Vec<[&str; 4]> = vec![
            ["tacos", "are", "tasty", "default_graph"],
            ["nachos", "are", "tasty", "default_graph"],
            ["nachos", "are", "food", "default_graph"],
        ];
        let rules = decl_rules::<&str, &str>(&[[
            &[[B("nachos"), B("are"), B("tasty"), B("default_graph")]],
            &[[B("nachos"), B("are"), B("food"), B("default_graph")]],
        ]]);
        let composite_claims = vec![["nachos", "are", "food", "default_graph"]];
        let proof = prove::<&str, &str>(&facts, &composite_claims, &rules).unwrap();
        assert_eq!(&proof, &vec![]);
    }

    #[test]
    fn unconditional_rule() {
        let facts: Vec<[&str; 4]> = vec![];
        let rules = decl_rules::<&str, &str>(&[[
            &[],
            &[[B("nachos"), B("are"), B("food"), B("default_graph")]],
        ]]);
        let composite_claims = vec![["nachos", "are", "food", "default_graph"]];
        let proof = prove::<&str, &str>(&facts, &composite_claims, &rules).unwrap();
        assert_eq!(
            &proof,
            &[RuleApplication {
                rule_index: 0,
                instantiations: vec![]
            }]
        );
    }
}
