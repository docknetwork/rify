use crate::reasoner::{Triple, TripleStore};
use crate::rule::{Entity, LowRule, Rule};
use crate::translator::Translator;
use alloc::collections::{BTreeMap, BTreeSet};
use core::convert::TryInto;
use core::fmt::{Debug, Display};

/// Locate a proof of some composite claims given the provied premises and rules.
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use rify::{
///     prove,
///     Entity::{Any, Exactly},
///     Rule, RuleApplication,
/// };
///
/// // (?a, is, awesome) ∧ (?a, score, ?s) -> (?a score, awesome)
/// let awesome_score_axiom = Rule::create(
///     vec![
///         [Any("a"), Exactly("is"), Exactly("awesome")], // if someone is awesome
///         [Any("a"), Exactly("score"), Any("s")],    // and they have some score
///     ],
///     vec![[Any("a"), Exactly("score"), Exactly("awesome")]], // then they must have an awesome score
/// )?;
///
/// assert_eq!(
///     prove::<&str, &str>(
///         &[["you", "score", "unspecified"], ["you", "is", "awesome"]],
///         &[["you", "score", "awesome"]],
///         &[awesome_score_axiom]
///     )?,
///     &[
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
    premises: &'a [[Bound; 3]],
    to_prove: &'a [[Bound; 3]],
    rules: &'a [Rule<Unbound, Bound>],
) -> Result<Vec<RuleApplication<Bound>>, CantProve> {
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
    let lpremises: Vec<Triple> = premises.iter().map(|spo| as_raw(spo).unwrap()).collect();
    let lto_prove: Vec<Triple> = to_prove
        .iter()
        .map(as_raw)
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
    premises: &[Triple],
    to_prove: &[Triple],
    rules: &[LowRule],
) -> Result<Vec<LowRuleApplication>, CantProve> {
    let mut ts = TripleStore::new();
    for prem in premises {
        ts.insert(prem.clone());
    }

    // statement (Triple) is proved by applying rule (LowRuleApplication)
    let mut arguments: BTreeMap<Triple, LowRuleApplication> = BTreeMap::new();

    // reason
    loop {
        if to_prove.iter().all(|tp| ts.contains(tp)) {
            break;
        }
        let mut to_add = BTreeSet::<Triple>::new();
        for (rule_index, rr) in rules.iter().enumerate() {
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
                            .or_insert_with(|| LowRuleApplication {
                                rule_index,
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
        return Err(CantProve::ExhaustedSearchSpace);
    }

    let mut ret: Vec<LowRuleApplication> = Vec::new();
    for claim in to_prove {
        recall_proof(claim, &mut arguments, rules, &mut ret);
    }
    Ok(ret)
}

// TODO, this fuction is not tail recursive
/// As this function populates the output. It removes correspond arguments from the input.
/// The reason being that a single argument does not need to be proved twice. Once is is
/// proved, it can be treated as a premise.
fn recall_proof<'a>(
    // globally scoped triple to prove
    to_prove: &Triple,
    arguments: &mut BTreeMap<Triple, LowRuleApplication>,
    rules: &[LowRule],
    outp: &mut Vec<LowRuleApplication>,
) {
    let to_global_scope = |rra: &LowRuleApplication, locally_scoped_entity: u32| -> u32 {
        let concrete = rules[rra.rule_index]
            .inst
            .as_ref()
            .get(&locally_scoped_entity);
        let found = rra.instantiations.get(&locally_scoped_entity);
        debug_assert!(if let (Some(c), Some(f)) = (concrete, found) {
            c == f
        } else {
            true
        });
        *concrete.or(found).unwrap()
    };

    if let Some(application) = arguments.remove(to_prove) {
        // for every required sub-statement, recurse
        for triple in &rules[application.rule_index].if_all {
            recall_proof(
                &Triple::from_tuple(
                    to_global_scope(&application, triple.subject.0),
                    to_global_scope(&application, triple.property.0),
                    to_global_scope(&application, triple.object.0),
                ),
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

#[derive(Clone, Debug, PartialEq, Eq)]
struct LowRuleApplication {
    rule_index: usize,
    instantiations: BTreeMap<u32, u32>,
}

impl LowRuleApplication {
    /// Panics
    ///
    /// This function will panic if:
    ///   - an unbound item from originial_rule is not instatiated by self
    ///   - or there is no translation for a global instatiation of one of the unbound entities in
    ///     original_rule.
    fn raise<Unbound: Ord, Bound: Ord + Clone>(
        &self,
        original_rule: &Rule<Unbound, Bound>,
        trans: &Translator<Bound>,
    ) -> RuleApplication<Bound> {
        let mut instantiations = Vec::new();

        // unbound_human -> unbound_local
        let uhul: BTreeMap<&Unbound, u32> = original_rule
            .cononical_unbound()
            .enumerate()
            .map(|(a, b)| (b, a.try_into().unwrap()))
            .collect();

        for unbound_human in original_rule.cononical_unbound() {
            let unbound_local = uhul[unbound_human];
            let bound_global = self.instantiations[&unbound_local];
            let bound_human = trans.back(bound_global).unwrap();
            instantiations.push(bound_human.clone());
        }

        RuleApplication {
            rule_index: self.rule_index,
            instantiations,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct RuleApplication<Bound> {
    /// The index of the rule in the implicitly associated rule list.
    pub rule_index: usize,
    /// Bindings for unbound names in the rule in order of appearance.
    pub instantiations: Vec<Bound>,
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::common::inc;
    use crate::rule::Entity::{Any, Exactly as Exa};

    #[test]
    fn novel_name() {
        assert_eq!(
            prove::<&str, &str>(&[], &[["andrew", "score", "awesome"]], &[]).unwrap_err(),
            CantProve::NovelName
        );
    }

    #[test]
    fn search_space_exhausted() {
        let err = prove::<&str, &str>(
            &[
                ["score", "score", "score"],
                ["andrew", "andrew", "andrew"],
                ["awesome", "awesome", "awesome"],
            ],
            &[["andrew", "score", "awesome"]],
            &[],
        )
        .unwrap_err();
        assert_eq!(err, CantProve::ExhaustedSearchSpace);
        let err = prove::<&str, &str>(
            &[
                ["score", "score", "score"],
                ["andrew", "andrew", "andrew"],
                ["awesome", "awesome", "awesome"],
                ["backflip", "backflip", "backflip"],
                ["ability", "ability", "ability"],
            ],
            &[["andrew", "score", "awesome"]],
            &[
                Rule::create(vec![], vec![]).unwrap(),
                Rule::create(
                    vec![[Any("a"), Exa("ability"), Exa("backflip")]],
                    vec![[Any("a"), Exa("score"), Exa("awesome")]],
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
                &[["doggo", "score", "11"]],
                &[["doggo", "score", "11"]],
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
                [Any("boi"), Exa("is"), Exa("awesome")], // if someone is awesome
                [Any("boi"), Exa("score"), Any("s")],    // and they have some score
            ],
            vec![[Any("boi"), Exa("score"), Exa("awesome")]], // then they must have an awesome score
        )
        .unwrap();
        assert_eq!(
            prove::<&str, &str>(
                &[["you", "score", "unspecified"], ["you", "is", "awesome"]],
                &[["you", "score", "awesome"]],
                &[awesome_score_axiom]
            )
            .unwrap(),
            vec![
                // (you is awesome) ∧ (you score unspecified) -> (you score awesome)
                RuleApplication {
                    rule_index: 0,
                    instantiations: vec!["you", "unspecified"]
                }
            ]
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

        let rules: Vec<Rule<&str, &str>> = {
            let ru: &[[&[[Entity<&str, &str>; 3]]; 2]] = &[
                [
                    &[
                        [Exa("andrew"), Exa("claims"), Any("c")],
                        [Any("c"), Exa("subject"), Any("s")],
                        [Any("c"), Exa("property"), Any("p")],
                        [Any("c"), Exa("object"), Any("o")],
                    ],
                    &[[Any("s"), Any("p"), Any("o")]],
                ],
                [
                    &[
                        [Any("person_a"), Exa("is"), Exa("awesome")],
                        [Any("person_a"), Exa("friendswith"), Any("person_b")],
                    ],
                    &[[Any("person_b"), Exa("is"), Exa("awesome")]],
                ],
                [
                    &[[Any("person_a"), Exa("friendswith"), Any("person_b")]],
                    &[[Any("person_b"), Exa("friendswith"), Any("person_a")]],
                ],
            ];
            ru.iter()
                .map(|[ifa, then]| Rule::create(ifa.to_vec(), then.to_vec()).unwrap())
                .collect()
        };
        let facts: &[[&str; 3]] = &[
            ["soyoung", "friendswith", "nick"],
            ["nick", "friendswith", "elina"],
            ["elina", "friendswith", "sam"],
            ["sam", "friendswith", "fausto"],
            ["fausto", "friendswith", "lovesh"],
            ["andrew", "claims", "_:claim1"],
            ["_:claim1", "subject", "lovesh"],
            ["_:claim1", "property", "is"],
            ["_:claim1", "object", "awesome"],
        ];
        let composite_claims: &[[&str; 3]] =
            &[["soyoung", "is", "awesome"], ["nick", "is", "awesome"]];
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
        assert_eq!(proof, expected_proof);
    }

    #[test]
    fn ancestry_high() {
        let mut next_uniq = 0u32;
        let parent = inc(&mut next_uniq);
        let ancestor = inc(&mut next_uniq);
        let nodes: Vec<u32> = (0usize..10).map(|_| inc(&mut next_uniq)).collect();
        let facts: Vec<[u32; 3]> = nodes
            .iter()
            .zip(nodes.iter().cycle().skip(1))
            .map(|(a, b)| [*a, parent, *b])
            .collect();
        let rules: &[[&[[Entity<&str, u32>; 3]]; 2]] = &[
            [
                &[[Any("a"), Exa(parent), Any("b")]],
                &[[Any("a"), Exa(ancestor), Any("b")]],
            ],
            [
                &[
                    [Any("a"), Exa(ancestor), Any("b")],
                    [Any("b"), Exa(ancestor), Any("c")],
                ],
                &[[Any("a"), Exa(ancestor), Any("c")]],
            ],
        ];
        let composite_claims = vec![
            [*nodes.first().unwrap(), ancestor, *nodes.last().unwrap()],
            [*nodes.last().unwrap(), ancestor, *nodes.first().unwrap()],
            [*nodes.first().unwrap(), ancestor, *nodes.first().unwrap()],
        ];
        prove::<&str, u32>(&facts, &composite_claims, &decl_rules(rules)).unwrap();
    }

    fn decl_rules<Unbound: Ord + Debug + Clone, Bound: Ord + Clone>(
        rs: &[[&[[Entity<Unbound, Bound>; 3]]; 2]],
    ) -> Vec<Rule<Unbound, Bound>> {
        rs.iter()
            .map(|[ifa, then]| Rule::create(ifa.to_vec(), then.to_vec()).unwrap())
            .collect()
    }
}
