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

    /// Find in this tuple store all possible valid instantiations of rule. Report the
    /// instantiations through a callback.
    /// TODO: This function is recursive, but not tail recursive. Rules that are too long may
    ///       consume the stack.
    pub fn apply(
        &self,
        rule: &mut [Quad],
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
