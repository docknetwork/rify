use crate::mapstack::MapStack;
use crate::vecset::VecSet;
use core::cmp::Ordering;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Quad(Subject, Property, Object, GraphName);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Subject(pub u32);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Property(pub u32);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Object(pub u32);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct GraphName(pub u32);

/// Bindings of slots within the context of a rule.
pub type Instantiations = MapStack<u32, u32>;

pub struct TripleStore {
    claims: Vec<Quad>,
    spog: VecSet<usize>,
    posg: VecSet<usize>,
    ospg: VecSet<usize>,
    gspo: VecSet<usize>,
    gpos: VecSet<usize>,
    gosp: VecSet<usize>,
}

type Spog = (Subject, Property, Object, GraphName);
type Posg = (Property, Object, Subject, GraphName);
type Ospg = (Object, Subject, Property, GraphName);
type Gspo = (GraphName, Subject, Property, Object);
type Gpos = (GraphName, Property, Object, Subject);
type Gosp = (GraphName, Object, Subject, Property);

impl TripleStore {
    pub fn new() -> Self {
        Self {
            claims: Vec::new(),
            spog: VecSet::new(),
            posg: VecSet::new(),
            ospg: VecSet::new(),
            gspo: VecSet::new(),
            gpos: VecSet::new(),
            gosp: VecSet::new(),
        }
    }

    pub fn contains(&self, triple: &Quad) -> bool {
        !filter(triple.clone(), self).is_empty()
    }

    pub fn insert(&mut self, triple: Quad) {
        if !self.contains(&triple) {
            let mut cl = core::mem::replace(&mut self.claims, Vec::new());
            cl.push(triple);
            let ni = cl.len() - 1; // new index
            self.spog.insert(ni, |a, b| Spog::qcmp(&cl[*a], &cl[*b]));
            self.posg.insert(ni, |a, b| Posg::qcmp(&cl[*a], &cl[*b]));
            self.ospg.insert(ni, |a, b| Ospg::qcmp(&cl[*a], &cl[*b]));
            self.gspo.insert(ni, |a, b| Gspo::qcmp(&cl[*a], &cl[*b]));
            self.gpos.insert(ni, |a, b| Gpos::qcmp(&cl[*a], &cl[*b]));
            self.gosp.insert(ni, |a, b| Gosp::qcmp(&cl[*a], &cl[*b]));
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
        .all(|w| w[0] == w[1]));
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
            match self.pop_strictest_requirement(rule, instantiations) {
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
                (strictest.0 .0, quad.0 .0),
                (strictest.1 .0, quad.1 .0),
                (strictest.2 .0, quad.2 .0),
                (strictest.3 .0, quad.3 .0),
            ];
            for (k, v) in &to_write {
                debug_assert!(
                    instantiations.as_ref().get(&k).unwrap_or(v) == v,
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
        self.search(
            inst.get(&pattern.0 .0).cloned().map(Subject),
            inst.get(&pattern.1 .0).cloned().map(Property),
            inst.get(&pattern.2 .0).cloned().map(Object),
            inst.get(&pattern.3 .0).cloned().map(GraphName),
        )
    }

    fn search(
        &self,
        s: Option<Subject>,
        p: Option<Property>,
        o: Option<Object>,
        g: Option<GraphName>,
    ) -> &[usize] {
        match (s, p, o, g) {
            (Some(s), Some(p), Some(o), Some(g)) => filter((s, p, o, g), self),
            (Some(s), Some(p), Some(o), None) => filter((s, p, o), self),
            (Some(s), Some(p), None, Some(g)) => filter((g, s, p), self),
            (Some(s), Some(p), None, None) => filter((s, p), self),
            (Some(s), None, Some(o), Some(g)) => filter((g, o, s), self),
            (Some(s), None, Some(o), None) => filter((o, s), self),
            (Some(s), None, None, Some(g)) => filter((g, s), self),
            (Some(s), None, None, None) => filter(s, self),
            (None, Some(p), Some(o), Some(g)) => filter((g, p, o), self),
            (None, Some(p), Some(o), None) => filter((p, o), self),
            (None, Some(p), None, Some(g)) => filter((g, p), self),
            (None, Some(p), None, None) => filter(p, self),
            (None, None, Some(o), Some(g)) => filter((g, o), self),
            (None, None, Some(o), None) => filter(o, self),
            (None, None, None, Some(g)) => filter(g, self),
            (None, None, None, None) => &self.spog.as_slice(),
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

/// And implementer of FastFilter can be used to select the matching portion of a triple store in
/// O(log n).
trait FastFilter {
    /// Return the slice with the ordering that this fastfilter type will use
    fn target(ts: &TripleStore) -> &VecSet<usize>;
}

fn filter<'a, FF>(f: FF, ts: &TripleStore) -> &[usize]
where
    Quad: Into<FF>,
    FF: Ord + FastFilter,
{
    FF::target(ts).range(|b| ts.claims[*b].clone().into().cmp(&f))
}

impl FastFilter for Quad {
    fn target(ts: &TripleStore) -> &VecSet<usize> {
        &ts.spog
    }
}

impl From<Quad> for (Subject, Property, Object, GraphName) {
    fn from(other: Quad) -> Self {
        let Quad(s, p, o, g) = other;
        (s, p, o, g)
    }
}

impl FastFilter for (Subject, Property, Object, GraphName) {
    fn target(ts: &TripleStore) -> &VecSet<usize> {
        &ts.spog
    }
}

impl From<Quad> for (Subject, Property, Object) {
    fn from(other: Quad) -> Self {
        let Quad(s, p, o, _) = other;
        (s, p, o)
    }
}

impl FastFilter for (Subject, Property, Object) {
    fn target(ts: &TripleStore) -> &VecSet<usize> {
        &ts.spog
    }
}

impl From<Quad> for (Subject, Property) {
    fn from(other: Quad) -> Self {
        let Quad(s, p, _, _) = other;
        (s, p)
    }
}

impl FastFilter for (Subject, Property) {
    fn target(ts: &TripleStore) -> &VecSet<usize> {
        &ts.spog
    }
}

impl From<Quad> for Subject {
    fn from(other: Quad) -> Self {
        let Quad(s, _, _, _) = other;
        s
    }
}

impl FastFilter for Subject {
    fn target(ts: &TripleStore) -> &VecSet<usize> {
        &ts.spog
    }
}

impl From<Quad> for (GraphName, Subject, Property, Object) {
    fn from(other: Quad) -> Self {
        let Quad(s, p, o, g) = other;
        (g, s, p, o)
    }
}

impl From<Quad> for (GraphName, Subject, Property) {
    fn from(other: Quad) -> Self {
        let Quad(s, p, _, g) = other;
        (g, s, p)
    }
}

impl FastFilter for (GraphName, Subject, Property) {
    fn target(ts: &TripleStore) -> &VecSet<usize> {
        &ts.gspo
    }
}

impl From<Quad> for (GraphName, Object, Subject, Property) {
    fn from(other: Quad) -> Self {
        let Quad(s, p, o, g) = other;
        (g, o, s, p)
    }
}

impl From<Quad> for (GraphName, Object, Subject) {
    fn from(other: Quad) -> Self {
        let Quad(s, _, o, g) = other;
        (g, o, s)
    }
}

impl FastFilter for (GraphName, Object, Subject) {
    fn target(ts: &TripleStore) -> &VecSet<usize> {
        &ts.gosp
    }
}

impl From<Quad> for (Object, Subject, Property, GraphName) {
    fn from(other: Quad) -> Self {
        let Quad(s, p, o, g) = other;
        (o, s, p, g)
    }
}

impl From<Quad> for (Object, Subject) {
    fn from(other: Quad) -> Self {
        let Quad(s, _, o, _) = other;
        (o, s)
    }
}

impl FastFilter for (Object, Subject) {
    fn target(ts: &TripleStore) -> &VecSet<usize> {
        &ts.ospg
    }
}

impl From<Quad> for (GraphName, Subject) {
    fn from(other: Quad) -> Self {
        let Quad(s, _, _, g) = other;
        (g, s)
    }
}

impl FastFilter for (GraphName, Subject) {
    fn target(ts: &TripleStore) -> &VecSet<usize> {
        &ts.gspo
    }
}

impl From<Quad> for (GraphName, Property, Object, Subject) {
    fn from(other: Quad) -> Self {
        let Quad(s, p, o, g) = other;
        (g, p, o, s)
    }
}

impl From<Quad> for (GraphName, Property, Object) {
    fn from(other: Quad) -> Self {
        let Quad(_, p, o, g) = other;
        (g, p, o)
    }
}

impl FastFilter for (GraphName, Property, Object) {
    fn target(ts: &TripleStore) -> &VecSet<usize> {
        &ts.gpos
    }
}

impl From<Quad> for (Property, Object, Subject, GraphName) {
    fn from(other: Quad) -> Self {
        let Quad(s, p, o, g) = other;
        (p, o, s, g)
    }
}

impl From<Quad> for (Property, Object) {
    fn from(other: Quad) -> Self {
        let Quad(_, p, o, _) = other;
        (p, o)
    }
}

impl FastFilter for (Property, Object) {
    fn target(ts: &TripleStore) -> &VecSet<usize> {
        &ts.posg
    }
}

impl From<Quad> for (GraphName, Property) {
    fn from(other: Quad) -> Self {
        let Quad(_, p, _, g) = other;
        (g, p)
    }
}

impl FastFilter for (GraphName, Property) {
    fn target(ts: &TripleStore) -> &VecSet<usize> {
        &ts.gpos
    }
}

impl From<Quad> for Property {
    fn from(other: Quad) -> Self {
        let Quad(_, p, _, _) = other;
        p
    }
}

impl FastFilter for Property {
    fn target(ts: &TripleStore) -> &VecSet<usize> {
        &ts.posg
    }
}

impl From<Quad> for (GraphName, Object) {
    fn from(other: Quad) -> Self {
        let Quad(_, _, o, g) = other;
        (g, o)
    }
}

impl FastFilter for (GraphName, Object) {
    fn target(ts: &TripleStore) -> &VecSet<usize> {
        &ts.gosp
    }
}

impl From<Quad> for Object {
    fn from(other: Quad) -> Self {
        let Quad(_, _, o, _) = other;
        o
    }
}

impl FastFilter for Object {
    fn target(ts: &TripleStore) -> &VecSet<usize> {
        &ts.ospg
    }
}

impl From<Quad> for GraphName {
    fn from(other: Quad) -> Self {
        let Quad(_, _, _, g) = other;
        g
    }
}

impl FastFilter for GraphName {
    fn target(ts: &TripleStore) -> &VecSet<usize> {
        &ts.gosp
    }
}

trait QuadOrder {
    fn qcmp(a: &Quad, b: &Quad) -> Ordering;
}

impl QuadOrder for Spog {
    fn qcmp(a: &Quad, b: &Quad) -> Ordering {
        let Quad(sa, pa, oa, ga) = a;
        let Quad(sb, pb, ob, gb) = b;
        (sa, pa, oa, ga).cmp(&(sb, pb, ob, gb))
    }
}

impl QuadOrder for Posg {
    fn qcmp(a: &Quad, b: &Quad) -> Ordering {
        let Quad(sa, pa, oa, ga) = a;
        let Quad(sb, pb, ob, gb) = b;
        (pa, oa, sa, ga).cmp(&(pb, ob, sb, gb))
    }
}

impl QuadOrder for Ospg {
    fn qcmp(a: &Quad, b: &Quad) -> Ordering {
        let Quad(sa, pa, oa, ga) = a;
        let Quad(sb, pb, ob, gb) = b;
        (oa, sa, pa, ga).cmp(&(ob, sb, pb, gb))
    }
}

impl QuadOrder for Gspo {
    fn qcmp(a: &Quad, b: &Quad) -> Ordering {
        let Quad(sa, pa, oa, ga) = a;
        let Quad(sb, pb, ob, gb) = b;
        (ga, sa, pa, oa).cmp(&(gb, sb, pb, ob))
    }
}

impl QuadOrder for Gpos {
    fn qcmp(a: &Quad, b: &Quad) -> Ordering {
        let Quad(sa, pa, oa, ga) = a;
        let Quad(sb, pb, ob, gb) = b;
        (ga, pa, oa, sa).cmp(&(gb, pb, ob, sb))
    }
}

impl QuadOrder for Gosp {
    fn qcmp(a: &Quad, b: &Quad) -> Ordering {
        let Quad(sa, pa, oa, ga) = a;
        let Quad(sb, pb, ob, gb) = b;
        (ga, oa, sa, pa).cmp(&(gb, ob, sb, pb))
    }
}
