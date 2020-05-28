extern crate core;

mod vecset;

enum Scoped<T> {
    Local(usize),
    Global(T),
}

struct Triple<T> {
    subject: T,
    property: T,
    object: T,
}

struct Rule<T> {
    if_all: Vec<Triple<Scoped<T>>>,
    then: Triple<Scoped<T>>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use vecset::VecSet;

    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
    struct Subj<T>(T);
    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
    struct Prop<T>(T);
    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
    struct Obje<T>(T);

    struct TripleStore<T: Ord> {
        claims: Vec<Triple<T>>,
        spo: VecSet<usize>,
        pos: VecSet<usize>,
        osp: VecSet<usize>,
    }

    struct Instantiation;

    impl<T: Ord + Clone> TripleStore<T> {
        fn insert(&mut self, triple: Triple<T>) {
            let new = self
                .spo
                .range(|e| as_spo(&self.claims[*e]).cmp(&as_spo(&triple)))
                .len()
                .eq(&0);
            if new {
                let mut claims = core::mem::replace(&mut self.claims, Vec::new());
                claims.push(triple);
                let new_index = claims.len();
                insert_transformed(&mut self.spo, new_index, |a| as_spo(&claims[*a]));
                insert_transformed(&mut self.pos, new_index, |a| as_pos(&claims[*a]));
                insert_transformed(&mut self.osp, new_index, |a| as_osp(&claims[*a]));
            }
        }

        /// Find in this tuple store all possible valid instantiations of rule. Report the
        /// consequences of all such instantiations through a callback.
        fn apply(&self, rule: Rule<T>, cb: impl FnMut(&Instantiation)) {
            // find the the requirement in the rule which has the smallest search space

            // If there is only one requirement left in the rule set, iterate through every possible
            // instantiation of that requirement.

            // For every possible concrete instantiation of that rule, pin the names to activate the
            // instantiation then recurse.
            unimplemented!()
        }

        /// Return a slice representing all possible matches to the pattern provided.
        fn matches(&self, pattern: Triple<Scoped<T>>) -> &[usize] {
            match pattern {
                Triple {
                    subject: Scoped::Global(s),
                    property: Scoped::Global(p),
                    object: Scoped::Global(o),
                } => self
                    .spo
                    .range(move |b| as_spo(&self.claims[*b]).cmp(&(Subj(&s), Prop(&p), Obje(&o)))),
                Triple {
                    subject: Scoped::Global(s),
                    property: Scoped::Global(p),
                    object: Scoped::Local(_),
                } => self
                    .spo
                    .range(move |b| as_sp(&self.claims[*b]).cmp(&(Subj(&s), Prop(&p)))),
                Triple {
                    subject: Scoped::Global(s),
                    property: Scoped::Local(_),
                    object: Scoped::Global(o),
                } => self
                    .osp
                    .range(move |b| as_os(&self.claims[*b]).cmp(&(Obje(&o), Subj(&s)))),
                Triple {
                    subject: Scoped::Global(s),
                    property: Scoped::Local(_),
                    object: Scoped::Local(_),
                } => self.spo.range(move |b| self.claims[*b].subject.cmp(&s)),
                Triple {
                    subject: Scoped::Local(_),
                    property: Scoped::Global(p),
                    object: Scoped::Global(o),
                } => self
                    .osp
                    .range(move |b| as_po(&self.claims[*b]).cmp(&(Prop(&p), Obje(&o)))),
                Triple {
                    subject: Scoped::Local(_),
                    property: Scoped::Global(p),
                    object: Scoped::Local(_),
                } => self.pos.range(move |b| self.claims[*b].property.cmp(&p)),
                Triple {
                    subject: Scoped::Local(_),
                    property: Scoped::Local(_),
                    object: Scoped::Global(o),
                } => self.osp.range(move |b| self.claims[*b].object.cmp(&o)),
                Triple {
                    subject: Scoped::Local(_),
                    property: Scoped::Local(_),
                    object: Scoped::Local(_),
                } => self.spo.as_slice(),
            }
        }
    }

    fn as_spo<T>(a: &Triple<T>) -> (Subj<&T>, Prop<&T>, Obje<&T>) {
        (Subj(&a.subject), Prop(&a.property), Obje(&a.object))
    }

    fn as_pos<T>(a: &Triple<T>) -> (Prop<&T>, Obje<&T>, Subj<&T>) {
        (Prop(&a.property), Obje(&a.object), Subj(&a.subject))
    }

    fn as_osp<T>(a: &Triple<T>) -> (Obje<&T>, Subj<&T>, Prop<&T>) {
        (Obje(&a.object), Subj(&a.subject), Prop(&a.property))
    }

    fn as_sp<T>(a: &Triple<T>) -> (Subj<&T>, Prop<&T>) {
        (Subj(&a.subject), Prop(&a.property))
    }

    fn as_po<T>(a: &Triple<T>) -> (Prop<&T>, Obje<&T>) {
        (Prop(&a.property), Obje(&a.object))
    }

    fn as_os<T>(a: &Triple<T>) -> (Obje<&T>, Subj<&T>) {
        (Obje(&a.object), Subj(&a.subject))
    }

    /// Add element to set, using S as a proxy type for ordering.
    fn insert_transformed<T, S: Ord>(set: &mut VecSet<T>, element: T, f: impl Fn(&T) -> S) {
        set.insert(element, |a, b| f(a).cmp(&f(b)))
    }

    #[test]
    fn ancestry() {}
}
