extern crate core;

mod mapstack;
mod vecset;

use crate::mapstack::MapStack;
use crate::vecset::VecSet;
use core::cmp::Ordering;

#[derive(Clone)]
pub struct Triple {
    subject: Subj,
    property: Prop,
    object: Obje,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Subj(u32);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Prop(u32);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Obje(u32);

impl Triple {
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

type Instantiations = MapStack<u32, u32>;

// // invariants held:
// //   if_all is not empty
// //   all keys in instantiations appear in if_all
// struct Rule {
//     if_all: Vec<Triple>,
//     instantiations: Instantiations,
//     implies: Triple,
// }

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

    pub fn insert(&mut self, triple: Triple) {
        let new = self.spo.range(|e| self.claims[*e].cmp_spo(&triple)).len() == 0;
        if new {
            let mut claims = core::mem::replace(&mut self.claims, Vec::new());
            claims.push(triple);
            let new_index = claims.len();
            self.spo
                .insert(new_index, |a, b| claims[*a].cmp_spo(&claims[*b]));
            self.pos
                .insert(new_index, |a, b| claims[*a].cmp_pos(&claims[*b]));
            self.osp
                .insert(new_index, |a, b| claims[*a].cmp_osp(&claims[*b]));
            self.claims = claims;
        }
    }

    /// Find in this tuple store all possible valid instantiations of rule. Report the
    /// instantiations through a callback.
    /// TODO: This function is recursive, but not tail recursive. Rules that are too long may
    ///       consume the stack.
    /// TODO: This function does not terminate because fully instantiated rules are never
    ///       pruned from if_all.
    pub fn apply(
        &self,
        if_all: &[Triple],
        instantiations: &mut Instantiations,
        cb: &mut impl FnMut(&Instantiations),
    ) {
        if if_all.is_empty() {
            cb(&instantiations);
            return;
        }

        // find the the requirement in the rule which has the smallest search space
        let index_smallest = (0..if_all.len())
            .min_by_key(|index| self.matches(&if_all[*index], instantiations).len())
            .expect("if_all to be empty");
        let smallest_subrule = &if_all[index_smallest];
        let smallest_space = self.matches(smallest_subrule, instantiations);

        // For every possible concrete instantiation of that rule, pin the names to activate the
        // instantiation, then recurse.
        for index in smallest_space {
            let triple = &self.claims[*index];
            let to_write = &[
                (smallest_subrule.subject.0, triple.subject.0),
                (smallest_subrule.property.0, triple.property.0),
                (smallest_subrule.object.0, triple.object.0),
            ];
            for (k, v) in to_write {
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
            self.apply(if_all, instantiations, cb);
            for _ in to_write {
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ancestry() {
        // initial facts: (0 parent 1), (1 parent 2), ... (n-1 parent n). (n parent 0)
        // rules: (?a parent ?b) -> (?a ancestor ?b)
        //        (?a ancestor ?b) and (?b ancestor ?c) -> (?a ancestor ?c)
        // expected logical result: for all a for all b (a ancestor b)
    }
}
