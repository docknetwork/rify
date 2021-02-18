use crate::mapstack::MapStack;
use crate::vecset::VecSet;
use core::cmp::Ordering;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Quad {
    pub s: Subj,
    pub p: Prop,
    pub o: Obje,
    pub g: Grap,
}

impl From<[usize; 4]> for Quad {
    fn from([s, p, o, g]: [usize; 4]) -> Self {
        Self {
            s: Subj(s),
            p: Prop(p),
            o: Obje(o),
            g: Grap(g),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Subj(pub usize);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Prop(pub usize);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Obje(pub usize);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Grap(pub usize);

type Spog = (Subj, Prop, Obje, Grap);
type Posg = (Prop, Obje, Subj, Grap);
type Ospg = (Obje, Subj, Prop, Grap);
type Gspo = (Grap, Subj, Prop, Obje);
type Gpos = (Grap, Prop, Obje, Subj);
type Gosp = (Grap, Obje, Subj, Prop);
type Spo = (Subj, Prop, Obje);
type Pos = (Prop, Obje, Subj);
type Osp = (Obje, Subj, Prop);
type Gsp = (Grap, Subj, Prop);
type Gpo = (Grap, Prop, Obje);
type Gos = (Grap, Obje, Subj);
type Sp = (Subj, Prop);
type Po = (Prop, Obje);
type Os = (Obje, Subj);
type Gs = (Grap, Subj);
type Gp = (Grap, Prop);
type Go = (Grap, Obje);
type S = (Subj,);
type P = (Prop,);
type O = (Obje,);
type G = (Grap,);

/// Bindings of slots within the context of a rule.
pub type Instantiations = MapStack<usize, usize>;

#[derive(Default)]
pub struct Reasoner {
    claims: Vec<Quad>,
    spog: VecSet<usize>,
    posg: VecSet<usize>,
    ospg: VecSet<usize>,
    gspo: VecSet<usize>,
    gpos: VecSet<usize>,
    gosp: VecSet<usize>,
}

impl Reasoner {
    pub fn contains(&self, quad: &Quad) -> bool {
        let Quad { s, p, o, g } = quad;
        !(*s, *p, *o, *g).search(self).is_empty()
    }

    pub fn insert(&mut self, quad: Quad) {
        if !self.contains(&quad) {
            self.claims.push(quad);
            let ni = self.claims.len() - 1;
            let cl = core::mem::replace(&mut self.claims, Vec::new());
            self.spog.insert(ni, |a, b| Spog::qord(&cl[*a], &cl[*b]));
            self.posg.insert(ni, |a, b| Posg::qord(&cl[*a], &cl[*b]));
            self.ospg.insert(ni, |a, b| Ospg::qord(&cl[*a], &cl[*b]));
            self.gspo.insert(ni, |a, b| Gspo::qord(&cl[*a], &cl[*b]));
            self.gpos.insert(ni, |a, b| Gpos::qord(&cl[*a], &cl[*b]));
            self.gosp.insert(ni, |a, b| Gosp::qord(&cl[*a], &cl[*b]));
            self.claims = cl;
        }
        debug_assert!([
            self.claims.len(),
            self.spog.as_slice().len(),
            self.posg.as_slice().len(),
            self.ospg.as_slice().len(),
            self.gspo.as_slice().len(),
            self.gpos.as_slice().len(),
            self.gosp.as_slice().len(),
        ]
        .windows(2)
        .all(|wn| wn[0] == wn[1]));
    }

    /// Find in this store all possible valid instantiations of rule. Report the
    /// instantiations through a callback.
    /// TODO: This function is recursive, but not tail recursive. Rules that are too long may
    ///       consume the stack.
    pub fn apply(
        &self,
        rule: &mut [Quad],
        instantiations: &mut Instantiations,
        cb: &mut impl FnMut(&Instantiations),
    ) {
        let st = self.pop_strictest_requirement(rule, instantiations);
        let (strictest, mut less_strict) = match st {
            Some(s) => s,
            None => {
                cb(instantiations);
                return;
            }
        };

        // For every possible concrete instantiation fulfilling the requirement, bind the slots
        // in the requirement to the instantiation then recurse.
        for index in self.matches(strictest, instantiations) {
            let quad = &self.claims[*index];
            let to_write = [
                (strictest.s.0, quad.s.0),
                (strictest.p.0, quad.p.0),
                (strictest.o.0, quad.o.0),
                (strictest.g.0, quad.g.0),
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
    fn matches(&self, pattern: &Quad, instantiations: &Instantiations) -> &[usize] {
        let inst = instantiations.as_ref();
        let pattern: (Option<Subj>, Option<Prop>, Option<Obje>, Option<Grap>) = (
            inst.get(&pattern.s.0).cloned().map(Subj),
            inst.get(&pattern.p.0).cloned().map(Prop),
            inst.get(&pattern.o.0).cloned().map(Obje),
            inst.get(&pattern.g.0).cloned().map(Grap),
        );
        match pattern {
            (Some(s), Some(p), Some(o), Some(g)) => (s, p, o, g).search(self),
            (Some(s), Some(p), Some(o), None) => (s, p, o).search(self),
            (Some(s), Some(p), None, Some(g)) => (g, s, p).search(self),
            (Some(s), Some(p), None, None) => (s, p).search(self),
            (Some(s), None, Some(o), Some(g)) => (g, o, s).search(self),
            (Some(s), None, Some(o), None) => (o, s).search(self),
            (Some(s), None, None, Some(g)) => (g, s).search(self),
            (Some(s), None, None, None) => (s,).search(self),
            (None, Some(p), Some(o), Some(g)) => (g, p, o).search(self),
            (None, Some(p), Some(o), None) => (p, o).search(self),
            (None, Some(p), None, Some(g)) => (g, p).search(self),
            (None, Some(p), None, None) => (p,).search(self),
            (None, None, Some(o), Some(g)) => (g, o).search(self),
            (None, None, Some(o), None) => (o,).search(self),
            (None, None, None, Some(g)) => (g,).search(self),
            (None, None, None, None) => self.spog.as_slice(),
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
        rule: &'rule mut [Quad],
        instantiations: &Instantiations,
    ) -> Option<(&'rule Quad, &'rule mut [Quad])> {
        let index_strictest = (0..rule.len())
            .min_by_key(|index| self.matches(&rule[*index], instantiations).len())?;
        rule.swap(0, index_strictest);
        let (strictest, less_strict) = rule.split_first_mut().expect("rule to be non-empty");
        Some((strictest, less_strict))
    }
}

trait Indexed {
    fn target(rs: &Reasoner) -> &VecSet<usize>;
    fn qcmp(&self, quad: &Quad) -> Ordering;

    fn search<'a>(&'_ self, rs: &'a Reasoner) -> &'a [usize] {
        Self::target(rs).range(|e| self.qcmp(&rs.claims[*e]).reverse())
    }
}

macro_rules! impl_indexed {
    ($t:ty, $idx:tt, ( $($fields:tt,)* )) => {
        impl Indexed for $t {
            fn target(rs: &Reasoner) -> &VecSet<usize> {
                &rs.$idx
            }

            fn qcmp(&self, quad: &Quad) -> Ordering {
                self.cmp(&($(quad. $fields,)*))
            }
        }
    };
}

impl_indexed!(Spog, spog, (s, p, o, g,));
impl_indexed!(Posg, posg, (p, o, s, g,));
impl_indexed!(Ospg, ospg, (o, s, p, g,));
impl_indexed!(Gspo, gspo, (g, s, p, o,));
impl_indexed!(Gpos, gpos, (g, p, o, s,));
impl_indexed!(Gosp, gosp, (g, o, s, p,));
impl_indexed!(Spo, spog, (s, p, o,));
impl_indexed!(Pos, posg, (p, o, s,));
impl_indexed!(Osp, ospg, (o, s, p,));
impl_indexed!(Gsp, gspo, (g, s, p,));
impl_indexed!(Gpo, gpos, (g, p, o,));
impl_indexed!(Gos, gosp, (g, o, s,));
impl_indexed!(Sp, spog, (s, p,));
impl_indexed!(Po, posg, (p, o,));
impl_indexed!(Os, ospg, (o, s,));
impl_indexed!(Gs, gspo, (g, s,));
impl_indexed!(Gp, gpos, (g, p,));
impl_indexed!(Go, gosp, (g, o,));
impl_indexed!(S, spog, (s,));
impl_indexed!(P, posg, (p,));
impl_indexed!(O, ospg, (o,));
impl_indexed!(G, gspo, (g,));

trait QuadOrder {
    fn qord(a: &Quad, b: &Quad) -> Ordering;
}

macro_rules! impl_quad_order {
    ($t:ty, ( $($fields:tt,)* )) => {
        impl QuadOrder for $t {
            fn qord(a: &Quad, b: &Quad) -> Ordering {
                ($(a. $fields,)*).cmp(&($(b. $fields,)*))
            }
        }
    };
}

impl_quad_order!(Spog, (s, p, o, g,));
impl_quad_order!(Posg, (p, o, s, g,));
impl_quad_order!(Ospg, (o, s, p, g,));
impl_quad_order!(Gspo, (g, s, p, o,));
impl_quad_order!(Gpos, (g, p, o, s,));
impl_quad_order!(Gosp, (g, o, s, p,));

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::inc;
    use crate::rule::{
        Entity::{self, Bound as B, Unbound as U},
        LowRule, Rule,
    };
    use crate::translator::Translator;
    use alloc::collections::{BTreeMap, BTreeSet};

    #[test]
    fn ancestry_raw() {
        #[derive(Clone, Debug)]
        struct Rule {
            if_all: Vec<Quad>,
            then: Vec<Quad>,
            inst: Instantiations,
        }

        // entities
        let mut count = 0usize;
        let parent = Prop(inc(&mut count));
        let ancestor = Prop(inc(&mut count));
        let nodes: Vec<_> = (0..4).map(|_| inc(&mut count)).collect();
        let default_graph = Grap(inc(&mut count));

        // initial facts: (n0 parent n1 dg), (n1 parent n2 dg), ... (n[l-2] parent n[l-1] dg)
        //                (n[l-1] parent n0 dg)
        // dg: default_graph
        let facts = nodes
            .iter()
            .zip(nodes.iter().cycle().skip(1))
            .map(|(a, b)| Quad {
                s: Subj(*a),
                p: parent,
                o: Obje(*b),
                g: default_graph,
            });

        // rules: (?a parent ?b ?g) -> (?a ancestor ?b ?g)
        //        (?a ancestor ?b ?g) and (?b ancestor ?c ?g) -> (?a ancestor ?c ?g)
        let rules = vec![
            // (?a parent ?b ?g) -> (?a ancestor ?b ?g)
            Rule {
                if_all: quads(&[[0, 1, 2, 4]]),
                then: quads(&[[0, 3, 2, 4]]),
                inst: [(1, parent.0), (3, ancestor.0)].iter().cloned().collect(),
            },
            // (?a ancestor ?b ?g) and (?b ancestor ?c ?g) -> (?a ancestor ?c ?g)
            Rule {
                if_all: quads(&[[1, 0, 2, 4], [2, 0, 3, 4]]),
                then: quads(&[[1, 0, 3, 4]]),
                inst: [(0, ancestor.0)].iter().cloned().collect(),
            },
        ];

        // expected logical result: for all a for all b (a ancestor b)
        let mut ts = Reasoner::default();
        for fact in facts {
            ts.insert(fact);
        }

        // This test only does one round of reasoning, no forward chaining. We will need a forward
        // chaining test eventually.
        let mut results = Vec::<BTreeMap<usize, usize>>::new();
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

        // We expect the first rule, (?a parent ?b ?g) -> (?a ancestor ?b ?g), to activate once for
        // every parent relation.
        // The second rule, (?a ancestor ?b ?g) and (?b ancestor ?c ?g) -> (?a ancestor ?c ?g),
        // should not activate because results from application of first rule have not been added
        // to the rdf store so there are there are are not yet any ancestry relations present.
        let mut expected_intantiations: Vec<BTreeMap<usize, usize>> = nodes
            .iter()
            .zip(nodes.iter().cycle().skip(1))
            .map(|(a, b)| {
                [
                    (0, *a),
                    (1, parent.0),
                    (2, *b),
                    (3, ancestor.0),
                    (4, default_graph.0),
                ]
                .iter()
                .cloned()
                .collect()
            })
            .collect();
        results.sort();
        expected_intantiations.sort();
        assert_eq!(results, expected_intantiations);
    }

    fn quads(qs: &[[usize; 4]]) -> Vec<Quad> {
        qs.iter()
            .map(|[s, p, o, g]| Quad {
                s: Subj(*s),
                p: Prop(*p),
                o: Obje(*o),
                g: Grap(*g),
            })
            .collect()
    }

    #[test]
    fn ancestry() {
        // load data
        let parent = "parent";
        let ancestor = "ancestor";
        let default_graph = "default_graph";
        let nodes: Vec<_> = (0..10).map(|a| format!("n{}", a)).collect();

        // create a translator to map human readable names to unique id
        let tran: Translator<&str> = nodes
            .iter()
            .map(AsRef::as_ref)
            .chain([parent, ancestor, default_graph].iter().cloned())
            .collect();

        // load rules
        let rules: &[[&[[Entity<&str, &str>; 4]]; 2]] = &[
            [
                &[[U("a"), B(parent), U("b"), U("g")]],
                &[[U("a"), B(ancestor), U("b"), U("g")]],
            ],
            [
                &[
                    [U("a"), B(ancestor), U("b"), U("g")],
                    [U("b"), B(ancestor), U("c"), U("g")],
                ],
                &[[U("a"), B(ancestor), U("c"), U("g")]],
            ],
        ];
        let mut rrs: Vec<LowRule> = rules.iter().map(|rule| low_rule(*rule, &tran)).collect();

        // load data into reasoner
        let mut ts = Reasoner::default();
        // initial facts: (n_a parent n_a+1), (n_last parent n_0)
        let initial_claims: Vec<[&str; 4]> = nodes
            .iter()
            .zip(nodes.iter().cycle().skip(1))
            .map(|(a, b)| [a.as_str(), parent, b.as_str(), default_graph])
            .collect();
        for [s, p, o, g] in &initial_claims {
            ts.insert(
                [
                    tran.forward(s).unwrap(),
                    tran.forward(p).unwrap(),
                    tran.forward(o).unwrap(),
                    tran.forward(g).unwrap(),
                ]
                .into(),
            );
        }

        // reason
        loop {
            let mut to_add = BTreeSet::<Quad>::new();
            for rule in rrs.iter_mut() {
                let mut if_all = &mut rule.if_all;
                let mut inst = &mut rule.inst;
                let then = &rule.then;
                ts.apply(&mut if_all, &mut inst, &mut |inst| {
                    for implied in then {
                        let inst = inst.as_ref();
                        let new: Quad = [
                            inst[&implied.s.0],
                            inst[&implied.p.0],
                            inst[&implied.o.0],
                            inst[&implied.g.0],
                        ]
                        .into();
                        if !ts.contains(&new) {
                            to_add.insert(new);
                        }
                    }
                });
            }
            if to_add.is_empty() {
                break;
            }
            for new in to_add.into_iter() {
                ts.insert(new);
            }
        }

        // convert results back to human readable tuples
        let claims: BTreeSet<[&str; 4]> = ts
            .claims
            .iter()
            .map(|Quad { s, p, o, g }| {
                [
                    *tran.back(s.0).unwrap(),
                    *tran.back(p.0).unwrap(),
                    *tran.back(o.0).unwrap(),
                    *tran.back(g.0).unwrap(),
                ]
            })
            .collect();

        // assert results
        let expected_claims: BTreeSet<[&str; 4]> = pairs(nodes.iter())
            .map(|(a, b)| [a.as_str(), ancestor, b.as_str(), default_graph])
            .chain(initial_claims.iter().cloned())
            .collect();
        assert_eq!(claims, expected_claims);
    }

    /// panics if an unbound name is implied
    /// panics if rule contains bound names that are not present in Translator
    fn low_rule(rule: [&[[Entity<&str, &str>; 4]]; 2], trans: &Translator<&str>) -> LowRule {
        let [if_all, then] = rule;
        Rule::<&str, &str>::create(if_all.to_vec(), then.to_vec())
            .unwrap()
            .lower(trans)
            .unwrap()
    }

    fn pairs<'a, T: 'a + Clone, I: 'a + Iterator<Item = T> + Clone>(
        inp: I,
    ) -> impl 'a + Iterator<Item = (T, T)> {
        inp.clone()
            .flat_map(move |a| inp.clone().map(move |b| (a.clone(), b)))
    }
}
