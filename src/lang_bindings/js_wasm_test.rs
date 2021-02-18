use super::js_wasm::Entity;
use super::js_wasm::RuleUnchecked;
use crate::prove::RuleApplication;
use serde_json::json;

type RulesInput = Vec<RuleUnchecked>;
type ClaimsInput = Vec<[String; 4]>;
type ProofInput = Vec<RuleApplication<String>>;

/// this dummy function ensures the above types are up-to-date
/// with the actual interface
fn _types_correct(r: RulesInput, c: ClaimsInput, p: ProofInput) -> ProofInput {
    super::js_wasm::validate_(r.clone(), p).unwrap();
    super::js_wasm::prove_(c.clone(), c, r).unwrap()
}

#[test]
fn ser_deser_rules() {
    let rules: RulesInput = vec![RuleUnchecked {
        if_all: vec![[
            Entity::Bound("a".into()),
            Entity::Bound("b".into()),
            Entity::Unbound("c".into()),
            Entity::Bound("g".into()),
        ]],
        then: vec![],
    }];
    let expected = json!([
        {
            "if_all": [
                [{"Bound": "a"}, {"Bound": "b"}, {"Unbound": "c"}, {"Bound": "g"}]
            ],
            "then": []
        }
    ]);

    assert_eq!(&serde_json::to_value(&rules).unwrap(), &expected);
    assert_eq!(
        serde_json::from_value::<RulesInput>(expected).unwrap(),
        rules
    );
}

#[test]
fn ser_deser_claims() {
    let rules: ClaimsInput = vec![["a".into(), "b".into(), "c".into(), "g".into()]];
    let expected = json!([["a", "b", "c", "g"]]);

    assert_eq!(&serde_json::to_value(&rules).unwrap(), &expected);
    assert_eq!(
        serde_json::from_value::<ClaimsInput>(expected).unwrap(),
        rules
    );
}

#[test]
fn ser_deser_proof() {
    let rules: ProofInput = vec![
        RuleApplication {
            rule_index: 0,
            instantiations: vec!["a".into(), "b".into(), "sdf".into()],
        },
        RuleApplication {
            rule_index: 1000000,
            instantiations: vec![],
        },
    ];
    let expected = json!([
        {
            "rule_index": 0,
            "instantiations": ["a", "b", "sdf"],
        },
        {
            "rule_index": 1000000,
            "instantiations": [],
        }
    ]);

    assert_eq!(&serde_json::to_value(&rules).unwrap(), &expected);
    assert_eq!(
        serde_json::from_value::<ProofInput>(expected).unwrap(),
        rules
    );
}
