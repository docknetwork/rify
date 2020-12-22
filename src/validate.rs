use crate::prove::BadRuleApplication;
use crate::{Claim, Rule, RuleApplication};
use alloc::collections::BTreeSet;

/// Check is a proof is well-formed according to a ruleset. Returns the set of assumptions used by
/// the proof and the set of statements those assumptions imply. If all the assumptions are true,
/// and then all the implied claims are true under the provided ruleset.
///
/// Validating a proof checks whether the proof is valid, but not whether implied claims are true.
/// Additional steps need to be performed to ensure the proof is true. You can use the following
/// statement to check soundness:
///
/// ```customlang
/// forall assumed, implied, rules, proof:
///   if Ok(Valid { assumed, implied }) = validate(rules, proof)
///   and all assumed are true
///   and all rules are true
///   then all implied are true
/// ```
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use rify::{
///     prove, validate, Valid,
///     Entity::{Bound, Unbound},
///     Rule, RuleApplication,
/// };
///
/// // (?a, is, awesome) ∧ (?a, score, ?s) -> (?a score, awesome)
/// let awesome_score_axiom = Rule::create(
///     vec![
///         [Unbound("a"), Bound("is"), Bound("awesome")], // if someone is awesome
///         [Unbound("a"), Bound("score"), Unbound("s")],  // and they have some score
///     ],
///     vec![[Unbound("a"), Bound("score"), Bound("awesome")]], // then they must have an awesome score
/// )?;
///
/// let proof = vec![
///     // (you is awesome) ∧ (you score unspecified) -> (you score awesome)
///     RuleApplication {
///         rule_index: 0,
///         instantiations: vec!["you", "unspecified"]
///     }
/// ];
///
/// let Valid { assumed, implied } = validate::<&str, &str>(
///     &[awesome_score_axiom],
///     &proof,
/// ).map_err(|e| format!("{:?}", e))?;
///
/// // Now we know that under the given rules, if all RDF triples in `assumed` are true, then all
/// // RDF triples in `implied` are also true.
/// # Ok(())
/// # }
/// ```
pub fn validate<Unbound: Ord + Clone, Bound: Ord + Clone>(
    rules: &[Rule<Unbound, Bound>],
    proof: &[RuleApplication<Bound>],
) -> Result<Valid<Bound>, Invalid> {
    let mut implied: BTreeSet<Claim<Bound>> = BTreeSet::new();
    let mut assumed: BTreeSet<Claim<Bound>> = BTreeSet::new();
    for app in proof {
        let rule = rules.get(app.rule_index).ok_or(Invalid::NoSuchRule)?;
        for assumption in app.assumptions_when_applied(rule)? {
            if !implied.contains(&assumption) {
                assumed.insert(assumption);
            }
        }
        for implication in app.implications_when_applied(rule)? {
            if !assumed.contains(&implication) {
                implied.insert(implication);
            }
        }
    }
    debug_assert!(assumed.is_disjoint(&implied));
    Ok(Valid { assumed, implied })
}

/// Given the rules which were passed, if all the claims in `assumed` are true then all the
/// claims in `implied` are true.
#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
pub struct Valid<Bound> {
    #[cfg_attr(
        feature = "serde",
        serde(bound(serialize = "Bound: Ord", deserialize = "Bound: Ord"))
    )]
    pub assumed: BTreeSet<Claim<Bound>>,
    pub implied: BTreeSet<Claim<Bound>>,
}

#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
pub enum Invalid {
    /// The Rule being applied expects a different number of name bindings.
    BadRuleApplication,
    /// The rule index was too large. The list of expected rules does not contain that many rules.
    NoSuchRule,
}

impl From<BadRuleApplication> for Invalid {
    fn from(_: BadRuleApplication) -> Self {
        Self::BadRuleApplication
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::common::{decl_rules, Bound, Unbound};
    use crate::prove::prove;

    #[test]
    fn irrelevant_facts_ignored() {
        let facts: Vec<Claim<&str>> = vec![["tacos", "are", "tasty"], ["nachos", "are", "tasty"]];
        let rules = decl_rules::<&str, &str>(&[[
            &[[Bound("nachos"), Bound("are"), Bound("tasty")]],
            &[[Bound("nachos"), Bound("are"), Bound("food")]],
        ]]);
        let composite_claims = vec![["nachos", "are", "food"]];
        let proof = prove(&facts, &composite_claims, &rules).unwrap();
        let Valid { assumed, implied } = validate(&rules, &proof).unwrap();
        assert_eq!(
            &assumed,
            &[["nachos", "are", "tasty"]].iter().cloned().collect()
        );
        for claim in composite_claims {
            assert!(implied.contains(&claim));
        }
    }

    #[test]
    fn bad_rule_application() {
        let facts: Vec<Claim<&str>> = vec![["a", "a", "a"]];
        let rules_v1 = decl_rules::<&str, &str>(&[[
            &[[Unbound("a"), Bound("a"), Bound("a")]],
            &[[Bound("b"), Bound("b"), Bound("b")]],
        ]]);
        let rules_v2 = decl_rules::<&str, &str>(&[[
            &[[Bound("a"), Bound("a"), Bound("a")]],
            &[[Bound("b"), Bound("b"), Bound("b")]],
        ]]);
        let composite_claims = vec![["b", "b", "b"]];
        let proof = prove(&facts, &composite_claims, &rules_v1).unwrap();
        let err = validate(&rules_v2, &proof).unwrap_err();
        assert_eq!(err, Invalid::BadRuleApplication);
    }

    #[test]
    fn no_such_rule() {
        let facts: Vec<Claim<&str>> = vec![["a", "a", "a"]];
        let rules = decl_rules::<&str, &str>(&[[
            &[[Bound("a"), Bound("a"), Bound("a")]],
            &[[Bound("b"), Bound("b"), Bound("b")]],
        ]]);
        let composite_claims = vec![["b", "b", "b"]];
        let proof = prove(&facts, &composite_claims, &rules).unwrap();
        let err = validate::<&str, &str>(&[], &proof).unwrap_err();
        assert_eq!(err, Invalid::NoSuchRule);
    }

    #[test]
    fn validate_manual_proof() {
        // Rules:
        // A. (andrew claims ?c) ∧ (?c subject ?s) ∧ (?c property ?p) ∧ (?c object ?o) -> (?s ?p ?o)
        // B. (?a favoriteFood ?b) -> (?a likes ?b) ∧ (?b type food)
        // C. (?f type food) ∧ (?a alergyFree true) -> (?a mayEat ?f)

        // Facts:
        // (alice favoriteFood beans)
        // (andrew claims _:claim1)
        // (_:claim1 subject bob)
        // (_:claim1 property alergyFree)
        // (_:claim1 object true)

        // Composite Claims:
        // (bob mayEat beans)

        // Manual proof:
        //
        // using rule B
        //   (alice favoriteFood beans)
        //   therefore (beans type food)
        //
        // using rule A
        //   (andrew claims _:claim1)
        //   ∧ (_:claim1 subject bob)
        //   ∧ (_:claim1 property alergyFree)
        //   ∧ (_:claim1 object true)
        //   therefore (bob alergyFree true)
        //
        // using rule C
        //   (beans type food)
        //   and (bob alergyFree true)
        //   therefore (bob mayEat beans)

        let rules = decl_rules(&[
            [
                &[
                    [Bound("andrew"), Bound("claims"), Unbound("c")],
                    [Unbound("c"), Bound("subject"), Unbound("s")],
                    [Unbound("c"), Bound("property"), Unbound("p")],
                    [Unbound("c"), Bound("object"), Unbound("o")],
                ],
                &[[Unbound("s"), Unbound("p"), Unbound("o")]],
            ],
            [
                &[[Unbound("a"), Bound("favoriteFood"), Unbound("f")]],
                &[
                    [Unbound("a"), Bound("likes"), Unbound("f")],
                    [Unbound("f"), Bound("type"), Bound("food")],
                ],
            ],
            [
                &[
                    [Unbound("f"), Bound("type"), Bound("food")],
                    [Unbound("a"), Bound("alergyFree"), Bound("true")],
                ],
                &[[Unbound("a"), Bound("mayEat"), Unbound("f")]],
            ],
        ]);
        let facts: &[Claim<&str>] = &[
            ["alice", "favoriteFood", "beans"],
            ["andrew", "claims", "_:claim1"],
            ["_:claim1", "subject", "bob"],
            ["_:claim1", "property", "alergyFree"],
            ["_:claim1", "object", "true"],
        ];
        let manual_proof = decl_proof(&[
            (1, &["alice", "beans"]),
            (0, &["_:claim1", "bob", "alergyFree", "true"]),
            (2, &["beans", "bob"]),
        ]);
        let Valid { assumed, implied } = validate(&rules, &manual_proof).unwrap();
        assert_eq!(assumed, facts.iter().cloned().collect());
        assert_eq!(
            implied,
            [
                ["alice", "likes", "beans"],
                ["beans", "type", "food"],
                ["bob", "alergyFree", "true"],
                ["bob", "mayEat", "beans"] // this is the claim we wished to prove
            ]
            .iter()
            .cloned()
            .collect()
        );
    }

    fn decl_proof<'a>(ep: &'a [(usize, &[&str])]) -> Vec<RuleApplication<&'a str>> {
        ep.iter()
            .map(|(rule_index, inst)| RuleApplication {
                rule_index: *rule_index,
                instantiations: inst.to_vec(),
            })
            .collect()
    }
}
