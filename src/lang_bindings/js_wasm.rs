extern crate wasm_bindgen;

use crate::Rule;
use wasm_bindgen::prelude::*;

/// TODO: don't panic
#[wasm_bindgen]
pub fn prove(
    premises: Box<[JsValue]>,
    to_prove: Box<[JsValue]>,
    rules: Box<[JsValue]>,
) -> Box<[JsValue]> {
    let premises: Vec<[String; 3]> = premises
        .iter()
        .map(JsValue::into_serde)
        .map(Result::unwrap)
        .collect();
    let to_prove: Vec<[String; 3]> = to_prove
        .iter()
        .map(JsValue::into_serde)
        .map(Result::unwrap)
        .collect();
    let rules: Vec<Rule<String, String>> = rules
        .iter()
        .map(|jsv| {
            let [if_all, then]: [Vec<[Entity; 3]>; 2] = jsv.into_serde().unwrap();
            let to_crate_ent = |ent: Vec<[Entity; 3]>| -> Vec<[crate::Entity<String, String>; 3]> {
                ent.into_iter()
                    .map(|[a, b, c]| [a.into(), b.into(), c.into()])
                    .collect()
            };
            Rule::create(to_crate_ent(if_all), to_crate_ent(then)).unwrap()
        })
        .collect();
    crate::prove(&premises, &to_prove, &rules)
        .unwrap()
        .into_iter()
        .map(|ra| {
            let ral: RuleApplication = ra.into();
            JsValue::from_serde(&ral).unwrap()
        })
        .collect()
}

#[derive(serde::Deserialize)]
enum Entity {
    Unbound(String),
    Bound(String),
}

impl From<Entity> for crate::Entity<String, String> {
    fn from(ent: Entity) -> Self {
        match ent {
            Entity::Unbound(unbound) => crate::Entity::Any(unbound),
            Entity::Bound(bound) => crate::Entity::Exactly(bound),
        }
    }
}

#[derive(serde::Serialize)]
pub struct RuleApplication {
    /// The index of the rule in the implicitly associated rule list.
    pub rule_index: usize,
    /// Bindings for unbound names in the rule in order of appearance.
    pub instantiations: Vec<String>,
}

impl From<crate::RuleApplication<String>> for RuleApplication {
    fn from(other: crate::RuleApplication<String>) -> Self {
        let crate::RuleApplication {
            rule_index,
            instantiations,
        } = other;
        RuleApplication {
            rule_index,
            instantiations,
        }
    }
}
