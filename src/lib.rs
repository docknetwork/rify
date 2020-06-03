use crate::mapstack::MapStack;

mod mapstack;
mod vecset;

enum Scoped<T> {
    Local(usize),
    Global(T),
}

#[derive(Clone)]
struct Triple {
    subject: Subj,
    property: Prop,
    object: Obje,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Subj(usize);
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Prop(usize);
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Obje(usize);

impl From<Triple> for (Subj, Prop, Obje) {
    fn from(other: Triple) -> Self {
        (other.subject, other.property, other.object)
    }
}
impl From<Triple> for (Prop, Obje, Subj) {
    fn from(other: Triple) -> Self {
        (other.property, other.object, other.subject)
    }
}
impl From<Triple> for (Obje, Subj, Prop) {
    fn from(other: Triple) -> Self {
        (other.object, other.subject, other.property)
    }
}
impl From<Triple> for (Subj, Prop) {
    fn from(other: Triple) -> Self {
        (other.subject, other.property)
    }
}
impl From<Triple> for (Prop, Obje) {
    fn from(other: Triple) -> Self {
        (other.property, other.object)
    }
}
impl From<Triple> for (Obje, Subj) {
    fn from(other: Triple) -> Self {
        (other.object, other.subject)
    }
}
impl From<Triple> for Prop {
    fn from(other: Triple) -> Self {
        other.property
    }
}
impl From<Triple> for Subj {
    fn from(other: Triple) -> Self {
        other.subject
    }
}
impl From<Triple> for Obje {
    fn from(other: Triple) -> Self {
        other.object
    }
}
impl Triple {
    fn spo(&self) -> (Subj, Prop, Obje) {
        self.clone().into()
    }
    fn pos(&self) -> (Prop, Obje, Subj) {
        self.clone().into()
    }
    fn osp(&self) -> (Obje, Subj, Prop) {
        self.clone().into()
    }
    fn sp(&self) -> (Subj, Prop) {
        self.clone().into()
    }
    fn po(&self) -> (Prop, Obje) {
        self.clone().into()
    }
    fn os(&self) -> (Obje, Subj) {
        self.clone().into()
    }
}

type Instantiations = MapStack<usize, usize>;

// invariants held:
//   if_all is not empty
//   all keys in instantiations appear in if_all
struct Rule {
    if_all: Vec<Triple>,
    instantiations: Instantiations,
    implies: Triple,
}

#[cfg(test)]
mod tests {
    use super::*;
    use vecset::VecSet;

    struct TripleStore {
        claims: Vec<Triple>,
        spo: VecSet<usize>,
        pos: VecSet<usize>,
        osp: VecSet<usize>,
    }

    impl TripleStore {
        fn insert(&mut self, triple: Triple) {
            let new = self
                .spo
                .range(|e| self.claims[*e].spo().cmp(&triple.spo()))
                .len()
                .eq(&0);
            if new {
                let mut claims = core::mem::replace(&mut self.claims, Vec::new());
                claims.push(triple);
                let new_index = claims.len();
                insert_transformed(&mut self.spo, new_index, |a| claims[*a].spo());
                insert_transformed(&mut self.pos, new_index, |a| claims[*a].pos());
                insert_transformed(&mut self.osp, new_index, |a| claims[*a].osp());
            }
        }

        /// Find in this tuple store all possible valid instantiations of rule. Report the
        /// instantiations through a callback.
        /// TODO: This function is recursive, but not tail recursive. Rules that are too long may
        ///       consume the stack.
        fn apply(
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
                (Some(s), Some(p), Some(o)) => {
                    self.spo.range(|b| self.claims[*b].spo().cmp(&(s, p, o)))
                }
                (Some(s), Some(p), None) => self.spo.range(|b| self.claims[*b].sp().cmp(&(s, p))),
                (Some(s), None, Some(o)) => self.osp.range(|b| self.claims[*b].os().cmp(&(o, s))),
                (None, Some(p), Some(o)) => self.pos.range(|b| self.claims[*b].po().cmp(&(p, o))),
                (Some(s), None, None) => self.spo.range(|b| self.claims[*b].subject.cmp(&s)),
                (None, Some(p), None) => self.pos.range(|b| self.claims[*b].property.cmp(&p)),
                (None, None, Some(o)) => self.osp.range(|b| self.claims[*b].object.cmp(&o)),
                (None, None, None) => self.spo.as_slice(),
            }
        }
    }

    /// Add element to set, using S as a proxy type for ordering.
    fn insert_transformed<T, S: Ord>(set: &mut VecSet<T>, element: T, f: impl Fn(&T) -> S) {
        set.insert(element, |a, b| f(a).cmp(&f(b)))
    }

    #[test]
    fn ancestry() {
        // initial facts: (0 parent 1), (1 parent 2), ... (n-1 parent n). (n parent 0)
        // rules: (?a parent ?b) -> (?a ancestor ?b)
        //        (?a ancestor ?b) and (?b ancestor ?c) -> (?a ancestor ?c)
        
        // expected logical result: for all a for all b (a ancestor b)
    }
}
