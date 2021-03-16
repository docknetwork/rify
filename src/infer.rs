use crate::common::{forward, vertices, LowRuleApplication};
use crate::reasoner::{Quad, Reasoner};
use crate::rule::{LowRule, Rule};
use crate::translator::Translator;
use crate::RuleApplication;
use alloc::collections::BTreeSet;

/// Make all possible inferences.
pub fn infer<Unbound: Ord + Clone, Bound: Ord + Clone>(
    premises: &[[Bound; 4]],
    rules: &[Rule<Unbound, Bound>],
) -> Vec<RuleApplication<Bound>> {
    let tran: Translator<Bound> = vertices(premises, rules).cloned().collect();
    let lpremises: Vec<Quad> = premises
        .iter()
        .map(|quad| forward(&tran, quad).unwrap())
        .collect();
    let lrules: Vec<LowRule> = rules
        .iter()
        .cloned()
        .map(|rule: Rule<Unbound, Bound>| -> LowRule { rule.lower(&tran).map_err(|_| ()).unwrap() })
        .collect();
    low_infer(&lpremises, &lrules)
        .iter()
        .enumerate()
        .map(|(i, lra)| lra.raise(&rules[i], &tran))
        .collect()
}

/// A version of infer that operates on lowered input an returns output in lowered form.
fn low_infer(premises: &[Quad], rules: &[LowRule]) -> Vec<LowRuleApplication> {
    let mut rs = Reasoner::default();
    for prem in premises {
        rs.insert(prem.clone().into());
    }

    let mut arguments: Vec<LowRuleApplication> = Default::default();

    loop {
        let mut to_add = BTreeSet::<Quad>::new();
        for (rule_index, rr) in rules.iter().enumerate() {
            rs.apply(&mut rr.if_all.clone(), &mut rr.inst.clone(), &mut |inst| {
                let mut novel = false;

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
                        novel |= to_add.insert(new_quad);
                    }
                }

                if novel {
                    arguments.push(LowRuleApplication {
                        rule_index,
                        instantiations: ins.clone(),
                    });
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

    debug_assert!(
        {
            let mut args = arguments.clone();
            args.sort_unstable();
            args.windows(2).all(|w| w[0] != w[1])
        },
        "results of inference should not contain duplicates"
    );

    arguments
}
