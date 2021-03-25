extern crate wasm_bindgen;

#[cfg(test)]
mod js_wasm_test;

use rify::InvalidRule;
use rify::Rule;
use rify::RuleApplication;
use serde::de::DeserializeOwned;
use wasm_bindgen::prelude::*;

/// Locate a proof of some composite claims given the provided premises and rules.
///
/// ```js
/// // (?a, is, awesome) ∧ (?a, score, ?s) -> (?a score, awesome)
/// let awesome_score_axiom = {
///     if_all: [
///         [{Unbound: "a"}, {Bound: "is"}, {Bound: "awesome"}, {Bound: "default_graph"}],
///         [{Unbound: "a"}, {Bound: "score"}, {Unbound: "s"}, {Bound: "default_graph"}],
///     ],
///     then: [
///         [{Unbound: "a"}, {Bound: "score"}, {Bound: "awesome"}, {Bound: "default_graph"}]
///     ],
/// };
/// let proof = prove(
///   [
///      ["you", "score", "unspecified", "default_graph"],
///      ["you", "is", "awesome", "default_graph"],
///   ],
///   [["you", "score", "awesome", "default_graph"]],
///   [awesome_score_axiom],
/// );
/// expect(proof).to.deep.equal([{
///     rule_index: 0,
///     instantiations: ["you", "unspecified"]
/// }])
/// ```
#[wasm_bindgen]
pub fn prove(
    premises: Box<[JsValue]>,
    to_prove: Box<[JsValue]>,
    rules: Box<[JsValue]>,
) -> Result<Box<[JsValue]>, JsValue> {
    let proof = prove_(
        deser_list(&premises)?,
        deser_list(&to_prove)?,
        deser_list(&rules)?,
    )?;
    Ok(ser_list(&proof))
}

pub fn prove_(
    premises: Vec<[String; 4]>,
    to_prove: Vec<[String; 4]>,
    rules: Vec<RuleUnchecked>,
) -> Result<Vec<RuleApplication<String>>, Error> {
    let rules = RuleUnchecked::check_all(rules)?;
    let proof =
        rify::prove::<String, String>(&premises, &to_prove, &rules).map_err(Into::<Error>::into)?;
    Ok(proof)
}

/// Check is a proof is well-formed according to a ruleset. Returns the set of assumptions used by
/// the proof and the set of statements those assumptions imply. If all the assumptions are true,
/// then all the implied claims are true under the provided ruleset.
///
/// To restate, validating a proof checks whether the proof is valid, but not whether implied
/// claims are true. Additional steps need to be performed to ensure the proof is true. You can use
/// the following statement to check soundness:
///
/// ```customlang
/// forall assumed, implied, rules, proof:
///   let { assumed, implied } = validate(rules, proof);
///   If validate() doesn't throw,
///   and all assumed are true
///   and all rules are true
///   then all implied are true
/// ```
///
/// ```js
/// // (?a, is, awesome) ∧ (?a, score, ?s) -> (?a score, awesome)
/// let awesome_score_axiom = {
///   if_all: [
///     [{ Unbound: "a" }, { Bound: "is" }, { Bound: "awesome" }, { Bound: "default_graph" }],
///     [{ Unbound: "a" }, { Bound: "score" }, { Unbound: "s" }, { Bound: "default_graph" }],
///   ],
///   then: [
///     [{ Unbound: "a" }, { Bound: "score" }, { Bound: "awesome" }, { Bound: "default_graph" }]
///   ],
/// };
/// let known_facts = [
///   ["you", "score", "unspecified", "default_graph"],
///   ["you", "is", "awesome", "default_graph"],
/// ];
/// let valid = validate(
///   [awesome_score_axiom],
///   [{
///     rule_index: 0,
///     instantiations: ["you", "unspecified"]
///   }],
/// );
/// expect(valid).to.deep.equal({
///   assumed: [
///     ["you", "is", "awesome", "default_graph"],
///     ["you", "score", "unspecified", "default_graph"],
///   ],
///   implied: [
///     ["you", "score", "awesome", "default_graph"],
///   ]
/// });
///
/// // now we check that all the assumptions made by the proof are known to be true
/// for (let f of valid.assumed) {
///   if (!known_facts.some(kf => JSON.stringify(kf) === JSON.stringify(f))) {
///     throw new Error("Proof makes an unverified assumption.");
///   }
/// }
///
/// // After verifying all the assumptions in the proof are true, we know that the
/// // quads in valid.implied are true with respect to the provided rules.
/// ```
#[wasm_bindgen]
pub fn validate(rules: Box<[JsValue]>, proof: Box<[JsValue]>) -> Result<JsValue, JsValue> {
    let valid = validate_(deser_list(&rules)?, deser_list(&proof)?)?;
    Ok(ser(&valid))
}

pub fn validate_(
    rules: Vec<RuleUnchecked>,
    proof: Vec<RuleApplication<String>>,
) -> Result<rify::Valid<String>, Error> {
    let rules = RuleUnchecked::check_all(rules)?;
    let valid = rify::validate::<String, String>(&rules, &proof)?;
    Ok(valid)
}

/// Make all possible true inferences given input premises and rules. This is open-ended reasoning.
///
/// ```js
/// // (?a, is, awesome) ∧ (?a, score, ?s) -> (?a score, awesome)
/// let awesome_score_axiom = {
///   if_all: [
///     [{ Unbound: "a" }, { Bound: "is" }, { Bound: "awesome" }, { Bound: "default_graph" }],
///     [{ Unbound: "a" }, { Bound: "score" }, { Unbound: "s" }, { Bound: "default_graph" }],
///   ],
///   then: [
///     [{ Unbound: "a" }, { Bound: "score" }, { Bound: "awesome" }, { Bound: "default_graph" }]
///   ],
/// };
/// let facts = [
///   ["you", "score", "unspecified", "default_graph"],
///   ["you", "is", "awesome", "default_graph"],
/// ];
/// let new_facts = infer(facts, [awesome_score_axiom]);
/// facts = facts.concat(new_facts);
/// expect(facts).to.deep.equal([
///   ["you", "score", "unspecified", "default_graph"],
///   ["you", "is", "awesome", "default_graph"],
///   ["you", "score", "awesome", "default_graph"],
/// ]);
/// ```
#[wasm_bindgen]
pub fn infer(premises: Box<[JsValue]>, rules: Box<[JsValue]>) -> Result<JsValue, JsValue> {
    Ok(ser(&infer_(deser_list(&premises)?, deser_list(&rules)?)?))
}

pub fn infer_(
    premises: Vec<[String; 4]>,
    rules: Vec<RuleUnchecked>,
) -> Result<Vec<[String; 4]>, Error> {
    let rules = RuleUnchecked::check_all(rules)?;
    Ok(rify::infer::<String, String>(&premises, &rules))
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, serde::Serialize, serde::Deserialize)]
pub enum Entity {
    Unbound(String),
    Bound(String),
}

impl From<Entity> for rify::Entity<String, String> {
    fn from(ent: Entity) -> Self {
        match ent {
            Entity::Unbound(unbound) => rify::Entity::Unbound(unbound),
            Entity::Bound(bound) => rify::Entity::Bound(bound),
        }
    }
}

#[derive(serde::Serialize, serde::Deserialize, Debug, PartialEq, Eq)]
pub enum Error {
    InputTypo,
    InvalidRule(InvalidRule<String>),
    CantProve(rify::CantProve),
    InvalidProof(rify::Invalid),
}

impl From<Error> for JsValue {
    fn from(e: Error) -> JsValue {
        JsValue::from_serde(&e).unwrap()
    }
}

impl From<InvalidRule<String>> for Error {
    fn from(other: InvalidRule<String>) -> Self {
        Error::InvalidRule(other)
    }
}

impl From<serde_json::Error> for Error {
    fn from(_: serde_json::Error) -> Error {
        Error::InputTypo
    }
}

impl From<rify::CantProve> for Error {
    fn from(other: rify::CantProve) -> Self {
        Error::CantProve(other)
    }
}

impl From<rify::Invalid> for Error {
    fn from(other: rify::Invalid) -> Self {
        Error::InvalidProof(other)
    }
}

/// Deserialize a list of js values into a list of rust values
fn deser_list<T: DeserializeOwned>(a: &[JsValue]) -> Result<Vec<T>, Error> {
    a.iter().map(|b| deser::<T>(b)).collect()
}

/// Deserialize a js value into a rust value
fn deser<T: DeserializeOwned>(a: &JsValue) -> Result<T, Error> {
    JsValue::into_serde(&a).map_err(Into::into)
}

/// Serialize a list of rust value into a list of js values
///
/// # Panics
///
/// Panics if input cannot be deserialived.
fn ser_list<T: serde::Serialize>(a: &[T]) -> Box<[JsValue]> {
    let ret: Vec<JsValue> = a.iter().map(ser).collect();
    ret.into()
}

/// Serialize a rust value into a js value
///
/// # Panics
///
/// Panics if input cannot be deserialived.
fn ser<T: serde::Serialize>(a: &T) -> JsValue {
    JsValue::from_serde(a).unwrap()
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct RuleUnchecked {
    pub if_all: Vec<[Entity; 4]>,
    pub then: Vec<[Entity; 4]>,
}

impl RuleUnchecked {
    fn check(self) -> Result<Rule<String, String>, Error> {
        let RuleUnchecked { if_all, then } = self;
        let if_all = if_all.into_iter().map(convert_claim).collect();
        let then = then.into_iter().map(convert_claim).collect();
        Rule::create(if_all, then).map_err(Into::into)
    }

    fn check_all(rus: Vec<RuleUnchecked>) -> Result<Vec<Rule<String, String>>, Error> {
        rus.into_iter().map(Self::check).collect()
    }
}

fn convert_claim<T, A: Into<T>>(claim: [A; 4]) -> [T; 4] {
    let [s, p, o, g] = claim;
    [s.into(), p.into(), o.into(), g.into()]
}
