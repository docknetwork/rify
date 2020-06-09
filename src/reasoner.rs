use crate::mapstack::MapStack;
use crate::vecset::VecSet;
use core::cmp::Ordering;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Triple {
    pub subject: Subj,
    pub property: Prop,
    pub object: Obje,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Subj(pub u32);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Prop(pub u32);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Obje(pub u32);

impl Triple {
    pub fn from_tuple(subject: u32, property: u32, object: u32) -> Self {
        Self {
            subject: Subj(subject),
            property: Prop(property),
            object: Obje(object),
        }
    }

    fn cmp_spo(&self, other: &Self) -> Ordering {
        (self.subject, self.property, self.object).cmp(&(
            other.subject,
            other.property,
            other.object,
        ))
    }

    fn cmp_pos(&self, other: &Self) -> Ordering {
        (self.property, self.object, self.subject).cmp(&(
            other.property,
            other.object,
            other.subject,
        ))
    }

    fn cmp_osp(&self, other: &Self) -> Ordering {
        (self.object, self.subject, self.property).cmp(&(
            other.object,
            other.subject,
            other.property,
        ))
    }

    fn cmp_sp(&self, other: (Subj, Prop)) -> Ordering {
        (self.subject, self.property).cmp(&other)
    }

    fn cmp_po(&self, other: (Prop, Obje)) -> Ordering {
        (self.property, self.object).cmp(&other)
    }

    fn cmp_os(&self, other: (Obje, Subj)) -> Ordering {
        (self.object, self.subject).cmp(&other)
    }
}

/// Bindings of slots within the context of a rule.
pub type Instantiations = MapStack<u32, u32>;

pub struct TripleStore {
    claims: Vec<Triple>,
    spo: VecSet<usize>,
    pos: VecSet<usize>,
    osp: VecSet<usize>,
}

impl TripleStore {
    pub fn new() -> Self {
        Self {
            claims: Vec::new(),
            spo: VecSet::new(),
            pos: VecSet::new(),
            osp: VecSet::new(),
        }
    }

    pub fn contains(&self, triple: &Triple) -> bool {
        self.spo
            .as_slice()
            .binary_search_by(|e| self.claims[*e].cmp_spo(&triple))
            .is_ok()
    }

    pub fn insert(&mut self, triple: Triple) {
        if !self.contains(&triple) {
            let mut claims = core::mem::replace(&mut self.claims, Vec::new());
            claims.push(triple);
            let ni = claims.len() - 1;
            self.spo.insert(ni, |a, b| claims[*a].cmp_spo(&claims[*b]));
            self.pos.insert(ni, |a, b| claims[*a].cmp_pos(&claims[*b]));
            self.osp.insert(ni, |a, b| claims[*a].cmp_osp(&claims[*b]));
            self.claims = claims;
        }
        debug_assert_eq!(self.spo.as_slice().len(), self.claims.len());
        debug_assert_eq!(self.pos.as_slice().len(), self.claims.len());
        debug_assert_eq!(self.osp.as_slice().len(), self.claims.len());
    }

    /// Find in this tuple store all possible valid instantiations of rule. Report the
    /// instantiations through a callback.
    /// TODO: This function is recursive, but not tail recursive. Rules that are too long may
    ///       consume the stack.
    pub fn apply(
        &self,
        rule: &mut [Triple],
        instantiations: &mut Instantiations,
        cb: &mut impl FnMut(&Instantiations),
    ) {
        let (strictest, mut less_strict) =
            if let Some(s) = self.pop_strictest_requirement(rule, instantiations) {
                s
            } else {
                cb(instantiations);
                return;
            };

        // For every possible concrete instantiation fulfilling the requirement, bind the slots
        // in the requirement to the instantiation then recurse.
        for index in self.matches(strictest, instantiations) {
            let triple = &self.claims[*index];
            let to_write = [
                (strictest.subject.0, triple.subject.0),
                (strictest.property.0, triple.property.0),
                (strictest.object.0, triple.object.0),
            ];
            for (k, v) in &to_write {
                debug_assert!(
                    if let Some(committed_v) = instantiations.as_ref().get(&k) {
                        committed_v == v
                    } else {
                        true
                    },
                    "rebinding of an instantiated value should never occur"
                );
                instantiations.write(*k, *v);
            }
            self.apply(&mut less_strict, instantiations, cb);
            for _ in &to_write {
                instantiations.undo().unwrap();
            }
        }
    }

    /// Return a slice representing all possible matches to the pattern provided.
    /// pattern is in a local scope. instantiations is a partial translation of that
    /// local scope to the global scope represented by self.claims
    fn matches(&self, pattern: &Triple, instantiations: &Instantiations) -> &[usize] {
        let inst = instantiations.as_ref();
        let pattern: (Option<Subj>, Option<Prop>, Option<Obje>) = (
            inst.get(&pattern.subject.0).cloned().map(Subj),
            inst.get(&pattern.property.0).cloned().map(Prop),
            inst.get(&pattern.subject.0).cloned().map(Obje),
        );
        match pattern {
            (Some(subject), Some(property), Some(object)) => self.spo.range(|b| {
                self.claims[*b].cmp_spo(&Triple {
                    subject,
                    property,
                    object,
                })
            }),
            (Some(s), Some(p), None) => self.spo.range(|b| self.claims[*b].cmp_sp((s, p))),
            (Some(s), None, Some(o)) => self.osp.range(|b| self.claims[*b].cmp_os((o, s))),
            (None, Some(p), Some(o)) => self.pos.range(|b| self.claims[*b].cmp_po((p, o))),
            (Some(s), None, None) => self.spo.range(|b| self.claims[*b].subject.cmp(&s)),
            (None, Some(p), None) => self.pos.range(|b| self.claims[*b].property.cmp(&p)),
            (None, None, Some(o)) => self.osp.range(|b| self.claims[*b].object.cmp(&o)),
            (None, None, None) => self.spo.as_slice(),
        }
    }

    /// Retrieve the requirement with the smallest number of possible instantiations from a rule.
    /// Return that requirement, along with a slice of the rule that contains every requirement
    /// except for the one that was retrieved.
    /// Return None if there are no requirements in the rule.
    ///
    /// This function changes the ordering of the rule.
    fn pop_strictest_requirement<'rule>(
        &self,
        rule: &'rule mut [Triple],
        instantiations: &Instantiations,
    ) -> Option<(&'rule Triple, &'rule mut [Triple])> {
        let index_strictest = (0..rule.len())
            .min_by_key(|index| self.matches(&rule[*index], instantiations).len())?;
        rule.swap(0, index_strictest);
        let (strictest, less_strict) = rule.split_first_mut().expect("rule to be non-empty");
        Some((strictest, less_strict))
    }

    /// Get the list of every claim that has been inserted so far.
    pub fn claims(&self) -> &[Triple] {
        &self.claims
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::inc;
    use alloc::collections::BTreeMap;

    #[test]
    fn ancestry_raw() {
        #[derive(Clone, Debug)]
        struct Rule {
            if_all: Vec<Triple>,
            then: Vec<Triple>,
            inst: Instantiations,
        }

        // entities
        let mut count = 0u32;
        let parent = inc(&mut count);
        let ancestor = inc(&mut count);
        let nodes: Vec<_> = (0..4).map(|_| inc(&mut count)).collect();

        // initial facts: (n0 parent n1), (n1 parent n2), ... (n[l-2] parent n[l-1])
        //                (n[l-1] parent n0)
        let facts: Vec<Triple> = nodes
            .iter()
            .zip(nodes.iter().cycle().skip(1))
            .map(|(a, b)| Triple {
                subject: Subj(*a),
                property: Prop(parent),
                object: Obje(*b),
            })
            .collect();

        // rules: (?a parent ?b) -> (?a ancestor ?b)
        //        (?a ancestor ?b) and (?b ancestor ?c) -> (?a ancestor ?c)
        let rules = vec![
            // (?a parent ?b) -> (?a ancestor ?b)
            Rule {
                if_all: vec![Triple {
                    subject: Subj(0),
                    property: Prop(1),
                    object: Obje(2),
                }],
                then: vec![Triple {
                    subject: Subj(0),
                    property: Prop(3),
                    object: Obje(2),
                }],
                inst: [(1u32, parent), (3u32, ancestor)].iter().cloned().collect(),
            },
            // (?a ancestor ?b) and (?b ancestor ?c) -> (?a ancestor ?c)
            Rule {
                if_all: vec![
                    Triple {
                        subject: Subj(1),
                        property: Prop(0),
                        object: Obje(2),
                    },
                    Triple {
                        subject: Subj(2),
                        property: Prop(0),
                        object: Obje(3),
                    },
                ],
                then: vec![Triple {
                    subject: Subj(1),
                    property: Prop(0),
                    object: Obje(3),
                }],
                inst: [(0u32, ancestor)].iter().cloned().collect(),
            },
        ];

        // expected logical result: for all a for all b (a ancestor b)
        let mut ts = TripleStore::new();
        for fact in facts {
            ts.insert(fact);
        }

        // This test only does one round of reasoning, no forward chaining. We will need a forward
        // chaining test eventually.
        let mut results = Vec::<BTreeMap<u32, u32>>::new();
        for rule in rules {
            let Rule {
                mut if_all,
                then: _,
                mut inst,
            } = rule.clone();
            ts.apply(&mut if_all, &mut inst, &mut |inst| {
                results.push(inst.as_ref().clone())
            });
        }

        // We expect the first rule, (?a parent ?b) -> (?a ancestor ?b), to activate once for every
        // parent relation.
        // The second rule, (?a ancestor ?b) and (?b ancestor ?c) -> (?a ancestor ?c), should not
        // activate because results from application of first rule have not been added to the rdf
        // store so there are there are are not yet any ancestry relations present.
        let mut expected_intantiations: Vec<BTreeMap<u32, u32>> = nodes
            .iter()
            .zip(nodes.iter().cycle().skip(1))
            .map(|(a, b)| {
                [(0, *a), (1, parent), (2, *b), (3, ancestor)]
                    .iter()
                    .cloned()
                    .collect()
            })
            .collect();
        results.sort();
        expected_intantiations.sort();
        assert_eq!(results, expected_intantiations);
    }
}
