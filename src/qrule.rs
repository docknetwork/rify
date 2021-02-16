//! The reasoner's rule representation is optimized machine use, not human use. Comprehending and
//! composing rules directly is difficult for humans. This module provides a human friendly rule
//! description datatype that can be lowered to the reasoner's rule representation.

use crate::qreasoner::{Instantiations, Quad};
use crate::translator::Translator;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::fmt::Debug;
use core::fmt::Display;

#[derive(Clone, Debug, PartialEq, Eq)]
// invariants held:
//   unbound names may not exists in `then` unless they exist also in `if_all`
//
// TODO: find a way to make fields non-public to protect invariant
pub(crate) struct LowRule {
    pub if_all: Vec<Quad>,    // contains locally scoped names
    pub then: Vec<Quad>,      // contains locally scoped names
    pub inst: Instantiations, // partially maps the local scope to some global scope
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
pub enum Entity<Unbound, Bound> {
    Unbound(Unbound),
    Bound(Bound),
}

impl<Unbound, Bound> Entity<Unbound, Bound> {
    pub fn as_unbound(&self) -> Option<&Unbound> {
        match self {
            Entity::Unbound(s) => Some(s),
            Entity::Bound(_) => None,
        }
    }

    pub fn as_bound(&self) -> Option<&Bound> {
        match self {
            Entity::Unbound(_) => None,
            Entity::Bound(s) => Some(s),
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
// invariants held:
//   unbound names may not exists in `then` unless they exist also in `if_all`
pub struct Rule<Unbound, Bound> {
    if_all: Vec<[Entity<Unbound, Bound>; 4]>,
    then: Vec<[Entity<Unbound, Bound>; 4]>,
}

impl<'a, Unbound: Ord + Clone, Bound: Ord> Rule<Unbound, Bound> {
    pub fn create(
        if_all: Vec<[Entity<Unbound, Bound>; 4]>,
        then: Vec<[Entity<Unbound, Bound>; 4]>,
    ) -> Result<Self, InvalidRule<Unbound>> {
        let unbound_if = if_all.iter().flatten().filter_map(Entity::as_unbound);
        let unbound_then = then.iter().flatten().filter_map(Entity::as_unbound);

        for th in unbound_then.clone() {
            if !unbound_if.clone().any(|ifa| ifa == th) {
                return Err(InvalidRule::UnboundImplied(th.clone()));
            }
        }

        Ok(Self { if_all, then })
    }

    pub(crate) fn lower(&self, tran: &Translator<Bound>) -> Result<LowRule, NoTranslation<&Bound>> {
        // There are three types of name at play here.
        // - human names are represented as Entities
        // - local names are local to the rule we are creating. they are represented as u32
        // - global names are from the translator. they are represented as u32

        // assign local names to each human name
        // local names will be in a continous range from 0.
        // smaller local names will represent unbound entities, larger ones will represent bound
        let mut next_local = 0usize;
        let unbound_map: BTreeMap<&Unbound, usize> = assign_ids(
            self.if_all.iter().flatten().filter_map(Entity::as_unbound),
            &mut next_local,
        );
        let bound_map = assign_ids(
            self.iter_entities().filter_map(Entity::as_bound),
            &mut next_local,
        );
        debug_assert!(
            bound_map.values().all(|bound_local| unbound_map
                .values()
                .all(|unbound_local| bound_local > unbound_local)),
            "unbound names are smaller than bound names"
        );
        debug_assert_eq!(
            (0..next_local).collect::<BTreeSet<usize>>(),
            unbound_map
                .values()
                .chain(bound_map.values())
                .cloned()
                .collect(),
            "no names slots are wasted"
        );
        debug_assert_eq!(
            next_local as usize,
            unbound_map.values().chain(bound_map.values()).count(),
            "no duplicate assignments"
        );

        // gets the local name for a human_name
        let local_name = |entity: &Entity<Unbound, Bound>| -> usize {
            match entity {
                Entity::Unbound(s) => unbound_map[s],
                Entity::Bound(s) => bound_map[s],
            }
        };
        // converts a human readable restriction list to a list of locally scoped machine oriented
        // restrictions
        let to_requirements = |hu: &[[Entity<Unbound, Bound>; 4]]| -> Vec<Quad> {
            hu.iter()
                .map(|[s, p, o, g]| {
                    [
                        local_name(&s),
                        local_name(&p),
                        local_name(&o),
                        local_name(&g),
                    ]
                    .into()
                })
                .collect()
        };

        Ok(LowRule {
            if_all: to_requirements(&self.if_all),
            then: to_requirements(&self.then),
            inst: bound_map
                .iter()
                .map(|(human_name, local_name)| {
                    let global_name: u32 =
                        tran.forward(human_name).ok_or(NoTranslation(*human_name))?;
                    Ok((*local_name, global_name as usize))
                })
                .collect::<Result<_, _>>()?,
        })
    }
}

impl<'a, Unbound: Ord, Bound> Rule<Unbound, Bound> {
    /// List the unique unbound names in this rule in order of appearance.
    pub(crate) fn cononical_unbound(&self) -> impl Iterator<Item = &Unbound> {
        let mut listed = BTreeSet::<&Unbound>::new();
        self.if_all
            .iter()
            .flatten()
            .filter_map(Entity::as_unbound)
            .filter_map(move |unbound| {
                if listed.contains(unbound) {
                    None
                } else {
                    listed.insert(unbound);
                    Some(unbound)
                }
            })
    }
}

impl<'a, Unbound, Bound> Rule<Unbound, Bound> {
    pub fn iter_entities(&self) -> impl Iterator<Item = &Entity<Unbound, Bound>> {
        self.if_all.iter().chain(self.then.iter()).flatten()
    }

    pub fn if_all(&self) -> &[[Entity<Unbound, Bound>; 4]] {
        &self.if_all
    }

    pub fn then(&self) -> &[[Entity<Unbound, Bound>; 4]] {
        &self.then
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
pub enum InvalidRule<Unbound> {
    /// Implied statements (part of the "then" property) must not contain unbound symbols that do
    /// not exist in the other side of the expression.
    ///
    /// Examples of rules that would cause this error:
    ///
    /// ```customlang
    /// // all statements are true
    /// -> (?a, ?a, ?a)
    ///
    /// // conditional universal statement
    /// (<sun> <enabled> <false>) -> (?a <color> <black>)
    /// ```
    UnboundImplied(Unbound),
}

impl<Unbound: Debug> Display for InvalidRule<Unbound> {
    fn fmt(&self, fmtr: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        Debug::fmt(self, fmtr)
    }
}

#[cfg(feature = "std")]
impl<Unbound> std::error::Error for InvalidRule<Unbound> where InvalidRule<Unbound>: Debug + Display {}

#[derive(Debug, Eq, PartialEq)]
/// The rule contains terms that have no corresponding entity in the translators target universe.
pub struct NoTranslation<T>(T);

// assign a unique id to each unique element in the input
// starts counting with the current next_id. As ids are assigned
// the next_id value is incremented so it always reperesents the next available id
fn assign_ids<T: Ord>(inp: impl Iterator<Item = T>, next_id: &mut usize) -> BTreeMap<T, usize> {
    let mut ret: BTreeMap<T, usize> = BTreeMap::new();
    for unbound in inp {
        ret.entry(unbound).or_insert_with(|| inc(next_id));
    }
    ret
}

fn inc(a: &mut usize) -> usize {
    *a += 1;
    *a - 1
}

#[cfg(test)]
mod test {
    use super::Entity::{Bound, Unbound};
    use super::*;
    use core::iter::FromIterator;

    #[test]
    fn similar_names() {
        // test rule
        // (?a <a> <b>) ->
        // ?a should be a separate entity from <a>

        let rule = Rule::<&str, &str> {
            if_all: vec![[Unbound("a"), Bound("a"), Unbound("b"), Unbound("g")]],
            then: vec![],
        };
        let trans: Translator<&str> = ["a"].iter().cloned().collect();
        let rr = rule.lower(&trans).unwrap();

        // ?a != <a>
        assert_ne!(rr.if_all[0].s.0, rr.if_all[0].p.0);
    }

    #[test]
    fn lower() {
        // rules: (?a parent ?b) -> (?a ancestor ?b)
        //        (?a ancestor ?b) and (?b ancestor ?c) -> (?a ancestor ?c)

        let trans: Translator<&str> = ["parent", "ancestor"].iter().cloned().collect();

        {
            let rulea = Rule::<u16, &str> {
                if_all: vec![[Unbound(0xa), Bound("parent"), Unbound(0xb), Unbound(0xc)]],
                then: vec![[Unbound(0xa), Bound("ancestor"), Unbound(0xb), Unbound(0xc)]],
            };

            let re_rulea = rulea.lower(&trans).unwrap();
            let keys = [
                re_rulea.if_all[0].s.0,
                re_rulea.if_all[0].p.0,
                re_rulea.if_all[0].o.0,
                re_rulea.if_all[0].g.0,
                re_rulea.then[0].s.0,
                re_rulea.then[0].p.0,
                re_rulea.then[0].o.0,
                re_rulea.then[0].g.0,
            ];
            let vals: Vec<Option<&str>> = keys
                .iter()
                .map(|local_name| {
                    re_rulea
                        .inst
                        .as_ref()
                        .get(&local_name)
                        .map(|global_name: &usize| trans.back(*global_name as u32).unwrap().clone())
                })
                .collect();
            assert_eq!(
                &vals,
                &[
                    None,
                    Some("parent"),
                    None,
                    None,
                    None,
                    Some("ancestor"),
                    None,
                    None,
                ]
            );

            let ifa = re_rulea.if_all;
            let then = re_rulea.then;
            assert_ne!(ifa[0].p.0, then[0].p.0); // "parent" != "ancestor"
            assert_eq!(ifa[0].s.0, then[0].s.0); // a == a
            assert_eq!(ifa[0].o.0, then[0].o.0); // b == b
        }

        {
            let ruleb = Rule::<&str, &str> {
                if_all: vec![
                    [Unbound("a"), Bound("ancestor"), Unbound("b"), Unbound("g")],
                    [Unbound("b"), Bound("ancestor"), Unbound("c"), Unbound("g")],
                ],
                then: vec![[Unbound("a"), Bound("ancestor"), Unbound("c"), Unbound("g")]],
            };

            let re_ruleb = ruleb.lower(&trans).unwrap();
            let keys = [
                re_ruleb.if_all[0].s.0,
                re_ruleb.if_all[0].p.0,
                re_ruleb.if_all[0].o.0,
                re_ruleb.if_all[0].g.0,
                re_ruleb.if_all[1].s.0,
                re_ruleb.if_all[1].p.0,
                re_ruleb.if_all[1].o.0,
                re_ruleb.if_all[1].g.0,
                re_ruleb.then[0].s.0,
                re_ruleb.then[0].p.0,
                re_ruleb.then[0].o.0,
                re_ruleb.then[0].g.0,
            ];
            let vals: Vec<Option<&str>> = keys
                .iter()
                .map(|local_name| {
                    re_ruleb
                        .inst
                        .as_ref()
                        .get(&local_name)
                        .map(|global_name: &usize| trans.back(*global_name as u32).unwrap().clone())
                })
                .collect();
            assert_eq!(
                &vals,
                &[
                    None,
                    Some("ancestor"),
                    None,
                    None,
                    None,
                    Some("ancestor"),
                    None,
                    None,
                    None,
                    Some("ancestor"),
                    None,
                    None,
                ]
            );

            let ifa = re_ruleb.if_all;
            let then = re_ruleb.then;
            assert_ne!(ifa[0].s.0, ifa[1].s.0); // a != b
            assert_ne!(ifa[0].o.0, then[0].o.0); // b != c

            // "ancestor" == "ancestor" == "ancestor"
            assert_eq!(ifa[0].p.0, ifa[1].p.0);
            assert_eq!(ifa[1].p.0, then[0].p.0);

            assert_eq!(ifa[0].s.0, then[0].s.0); // a == a
            assert_eq!(ifa[1].o.0, then[0].o.0); // b == b
        }
    }

    #[test]
    fn lower_no_translation_err() {
        let trans = Translator::<&str>::from_iter(vec![]);

        let r = Rule::create(
            vec![[Unbound("a"), Bound("unknown"), Unbound("b"), Unbound("g")]],
            vec![],
        )
        .unwrap();
        let err = r.lower(&trans).unwrap_err();
        assert_eq!(err, NoTranslation(&"unknown"));

        let r = Rule::<&str, &str>::create(
            vec![],
            vec![[
                Bound("unknown"),
                Bound("unknown"),
                Bound("unknown"),
                Bound("unknown"),
            ]],
        )
        .unwrap();
        let err = r.lower(&trans).unwrap_err();
        assert_eq!(err, NoTranslation(&"unknown"));
    }

    #[test]
    fn create_invalid() {
        use Bound as B;
        use Unbound as U;

        Rule::<&str, &str>::create(vec![], vec![[U("a"), U("a"), U("a"), U("a")]]).unwrap_err();

        // Its unfortunate that this one is illegal but I have yet to find a way around the
        // limitation. Can you figure out how to do this safely?
        //
        // if [super? claims [minor? mayclaim pred?]]
        // and [minor? claims [s? pred? o?]]
        // then [super? claims [s? pred? o?]]
        //
        // The problem is that "then" clauses aren't allowed to create new entities. A new entity is
        // needed in order to state that last line. Example:
        //
        let ret = Rule::<&str, &str>::create(
            vec![
                // if [super? claims [minor? mayclaim pred?] g?]
                [U("super"), B("claims"), U("claim1"), U("g")],
                [U("claim1"), B("subject"), U("minor"), U("g")],
                [U("claim1"), B("predicate"), B("mayclaim"), U("g")],
                [U("claim1"), B("object"), U("pred"), U("g")],
                // and [minor? claims [s? pred? o?] g?]
                [U("minor"), B("claims"), U("claim2"), U("g")],
                [U("claim2"), B("subject"), U("s"), U("g")],
                [U("claim2"), B("predicate"), U("pred"), U("g")],
                [U("claim2"), B("object"), U("o"), U("g")],
            ],
            vec![
                // then [super? claims [s? pred? o?] g?]
                [U("super"), B("claims"), U("claim3"), U("g")],
                [U("claim3"), B("subject"), U("s"), U("g")],
                [U("claim3"), B("predicate"), U("pred"), U("g")],
                [U("claim3"), B("object"), U("o"), U("g")],
            ],
        );
        assert_eq!(ret, Err(InvalidRule::UnboundImplied("claim3")));

        // Watch out! You may think that the following is a valid solution, but it's not.
        //
        // DANGEROUS, do not use without further consideration:
        //
        // ```
        // if [super? claims c1?]
        // and [c1? subject minor?]
        // and [c1? predicate mayclaim]
        // and [c1? object pred?]
        //
        // and [minor? claims c2?]
        // and [c2? subject s?]
        // and [c2? predicate pred?]
        // and [c2? object o?]
        //
        // then [super? claims c2?]
        // ```
        //
        // This is potentially dangerously incorrect because c2? may have any number of other
        // subjects, predicates, or objects. Consider if the following were premises:
        //
        // ```
        // [alice claims _:c1]
        // [_:c1 subject s?]
        // [_:c1 predicate mayclaim]
        // [_:c1 object maysit]
        //
        // [bob claims _:c2]
        // [_:c2 subject charlie]
        // [_:c2 predicate maysit]
        // [_:c2 predicate owns]
        // [_:c2 object chair]
        // ```
        //
        // With these premises, it can be proven that [alice claims [charlie owns chair]]
        // even though alice only intendend to let [alice claims [charlie maysit chair]]
        //
        // Question: Is it possible to guard against these tricky premises?
    }

    #[test]
    fn serde() {
        #[derive(Debug, serde::Serialize, serde::Deserialize, PartialEq, Eq)]
        enum Term {
            Blank(String),
            Iri(String),
            Literal {
                value: String,
                datatype: String,
                #[serde(skip_serializing_if = "Option::is_none")]
                language: Option<String>,
            },
            DefaultGraph,
        }

        let jsonrule = serde_json::json![{
            "if_all": [
                [
                    { "Unbound": "pig" },
                    { "Bound": { "Iri": "https://example.com/Ability" } },
                    { "Bound": { "Iri": "https://example.com/Flight" } },
                    { "Bound": "DefaultGraph" },
                ],
                [
                    { "Unbound": "pig" },
                    { "Bound": { "Iri": "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" } },
                    { "Bound": { "Iri": "https://example.com/Pig" } },
                    { "Bound": "DefaultGraph" },
                ],
            ],
            "then": [
                [
                    { "Bound": { "Iri": "did:dock:bddap" } },
                    { "Bound": { "Iri": "http://xmlns.com/foaf/spec/#term_firstName" } },
                    {
                        "Bound": {
                            "Literal": {
                                "value": "Gorgadon",
                                "datatype": "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral",
                            },
                        },
                    },
                    { "Bound": "DefaultGraph" },
                ],
            ],
        }];

        let rule = Rule::<String, Term> {
            if_all: vec![
                [
                    Entity::Unbound("pig".to_string()),
                    Entity::Bound(Term::Iri("https://example.com/Ability".to_string())),
                    Entity::Bound(Term::Iri("https://example.com/Flight".to_string())),
                    Entity::Bound(Term::DefaultGraph),
                ],
                [
                    Entity::Unbound("pig".to_string()),
                    Entity::Bound(Term::Iri(
                        "http://www.w3.org/1999/02/22-rdf-syntax-ns#type".to_string(),
                    )),
                    Entity::Bound(Term::Iri("https://example.com/Pig".to_string())),
                    Entity::Bound(Term::DefaultGraph),
                ],
            ],
            then: vec![[
                Entity::Bound(Term::Iri("did:dock:bddap".to_string())),
                Entity::Bound(Term::Iri(
                    "http://xmlns.com/foaf/spec/#term_firstName".to_string(),
                )),
                Entity::Bound(Term::Literal {
                    value: "Gorgadon".to_string(),
                    datatype: "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral".to_string(),
                    language: None,
                }),
                Entity::Bound(Term::DefaultGraph),
            ]],
        };

        assert_eq!(
            &serde_json::from_value::<Rule::<String, Term>>(jsonrule.clone()).unwrap(),
            &rule
        );
        assert_eq!(
            &jsonrule,
            &serde_json::to_value::<Rule::<String, Term>>(rule).unwrap()
        );
    }
}
