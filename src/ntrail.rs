extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::lit::*;
use crate::assignments::*;
use crate::formula::*;
use crate::clause::*;
use crate::logic::*;

#[derive(Copy, Clone)]
pub enum Reason {
    Undefined,
    Decision,
    Unit,
    Long(usize),
}

/*
pub struct Trail {
    pub trail: Vec<Lit>,
    pub vardata: Vec<(usize, Reason)>,
}
*/
pub struct Step {
    pub lit: Lit,
    pub decision_level: usize,
    pub reason: Reason,
}

//const UNASSIGNED: usize = usize::MAX;

pub struct NTrail {
    //pub assignments: Vec<AssignedState>,
    pub assignments: Assignments,
    lit_to_level: Vec<usize>, // usize::MAX if unassigned
    trail: Vec<Step>,

    /// Trail indices of decisions.
    ///
    /// The first entry does not represent a decision and is fixed at 0 so that each entry on the
    /// trail has a preceding entry in this list and so that the decision at level `n` corresponds
    /// to the index `n`.
    decisions: Vec<usize>,
}

impl Reason {
    #[predicate]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            match self {
                Reason::Long(i) => 0 <= @i && @i < (@f.clauses).len(),
                _ => true
            }
        }
    }
}

#[logic]
#[requires(s.len() > 0)]
pub fn pop<T>(s: Seq<T>) -> Seq<T> {
    pearlite! {
        s.subsequence(0, s.len() - 1)
    }
}

#[logic]
#[requires(s.len() > 0)]
fn last_idx<T>(s: Seq<T>) -> Int {
    pearlite! { s.len()-1 }
}

#[logic]
#[requires(s.len() > 0)]
fn last_elem<T>(s: Seq<T>) -> T {
    pearlite! { s[s.len()-1] }
}

impl Step {
    #[predicate]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            self.lit.invariant(@f.num_vars) &&
            //self.decision_level >= 0 &&
            self.reason.invariant(f)
            //self.reason != Reason::Undefined
        }
    }
}

#[predicate]
fn crefs_in_range(trail: Seq<Step>, f: Formula) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < trail.len() ==>
            trail[i].invariant(f)
    }
}

#[predicate]
fn trail_invariant(trail: Seq<Step>, f: Formula) -> bool {
    pearlite! {
        trail.len() <= @f.num_vars &&
        crefs_in_range(trail, f)
    }
}

impl NTrail {
    #[predicate]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            self.assignments.invariant(f) &&
            trail_invariant(@self.trail, f)
        }
    }

    #[predicate]
    pub fn is_backtrackable(self, f: Formula) -> bool {
        pearlite! {
            long_are_post_unit_inner(@self.trail, f, @self.assignments) ==>
            long_are_post_unit_inner(pop((@self.trail)), f, (@self.assignments).set(@last_elem(@self.trail).lit.idx, 3u8))
        }
    }

    #[predicate]
    pub fn lit_not_in_less(self, f: Formula) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self.trail).len() ==>
                forall<j: Int> 0 <= j && j < i ==>
                match (@self.trail)[j].reason {
                    Reason::Long(cref) => !(@self.trail)[i].lit.lit_idx_in((@f.clauses)[@cref]),
                    _ => true,
                }
        }
    }

    // Trail does not contail duplicate idxes
    #[predicate]
    pub fn lit_is_unique(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self.trail).len() ==>
                forall<j: Int> 0 <= j && j < i ==>
                (@self.trail)[j].lit.idx != (@self.trail)[i].lit.idx
        }
    }

    #[trusted] // TODO
    #[requires((@self.trail).len() > 0)]
    #[requires(self.invariant(*f))]
    #[requires(self.lit_not_in_less(*f))]
    #[requires(self.lit_is_unique())]
    #[requires(long_are_post_unit_inner(@self.trail, *f, @self.assignments))]
    #[ensures(long_are_post_unit_inner((@(^self).trail), *f, (@(^self).assignments)))]
    fn backstep(&mut self, f: &Formula) {
        let last = self.trail.pop();
        match last {
            Some(step) => {
                self.assignments.0[step.lit.idx] = 3;
                //self.lit_to_level[step.lit.idx] = usize::MAX;
            }
            None => {
                panic!();
            }
        }

    }
}

#[trusted] // OK
#[logic]
#[requires(a.invariant(f))]
#[requires(f.invariant())]
#[requires(lit.invariant(@f.num_vars))]
#[ensures(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    ((@f.clauses)[i].post_unit_inner(@a) && !lit.lit_idx_in((@f.clauses)[i])) ==> 
    (@f.clauses)[i].post_unit_inner((@a).set(@lit.idx, 3u8))
)]
fn lemma_assign_maintains_test(f: Formula, a: Assignments, lit: Lit) {}

// OK to pop, but need to fix wipe. 
#[trusted] // OK
#[logic]
#[requires(t.invariant(f))]
#[requires(t.lit_not_in_less(f))]
#[requires(t.lit_is_unique())]
#[requires((@t.trail).len() > 0)]
#[requires(long_are_post_unit_inner(@t.trail, f, @t.assignments))]
/*
#[requires(forall<i: Int> 0 <= i && i < (@t.trail).len() - 1 ==>
    !l.lit_idx_in((@f.clauses)[@(@t.trail)[i].lit.idx])
)]
*/
//#[requires(forall<i: Int> 0 <= i && i < (@t.trail).len() - 1 ==>
//    !l.lit_in((@f.clauses)[@(@t.trail)[i].lit.idx])
//)]
//#[ensures(long_are_post_unit_inner((@t.trail).subsequence(0,(@t.trail).len() - 1), f, 
//(@t.assignments).set(@(@t.trail)[(@t.trail).len() - 1].lit.idx, 3u8)))]
#[ensures(long_are_post_unit_inner((@t.trail).subsequence(0,(@t.trail).len() - 1), f, 
@t.assignments))]
#[requires(l === (@t.trail)[(@t.trail).len() - 1].lit)]
fn lemma_pop_no_unass_is_ok(t: NTrail, f: Formula, l: Lit) {
    lemma_assign_maintains_test(f, t.assignments, l)
}

//#[trusted] // OK
#[logic]
#[requires(a.invariant(f))]
#[requires(f.invariant())]
#[requires(trail_invariant(v, f))]
#[requires(crefs_in_range(v, f))]
#[requires(lit.invariant(@f.num_vars))]
#[requires(unset((@a)[@lit.idx]))]
#[requires(long_are_post_unit_inner(v, f, @a))]
#[requires(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    (@f.clauses)[i].post_unit_inner(@a) ==> 
    (@f.clauses)[i].post_unit_inner((@a).set(@lit.idx, 1u8))
)]
#[requires(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    (@f.clauses)[i].post_unit_inner(@a) ==> 
    (@f.clauses)[i].post_unit_inner((@a).set(@lit.idx, 0u8)) 
)]
#[ensures(long_are_post_unit_inner(v, f, (@a).set(@lit.idx, 1u8)))]
#[ensures(long_are_post_unit_inner(v, f, (@a).set(@lit.idx, 0u8)))]
fn lemma_assign_newest(v: Seq<Step>, f: Formula, a: Assignments, lit: Lit) {}

//#[trusted] // OK
#[logic]
//#[requires(trail_invariant(v, f))]
//#[requires(crefs_in_range(v, f))]
//#[requires(a.invariant(f))] 
#[requires(t.invariant(f))]
#[requires(f.invariant())]
#[requires(lit.invariant(@f.num_vars))]
//#[requires(unset((@a)[@lit.idx]))]
#[requires(forall<i: Int> 0 <= i && i < (@t.trail).len() ==>
    !lit.lit_idx_in((@f.clauses)[@(@t.trail)[i].lit.idx])
)]
#[ensures(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    (@f.clauses)[i].post_unit_inner(@t.assignments) ==> 
    (@f.clauses)[i].post_unit_inner((@t.assignments).set(@lit.idx, 3u8))
)]
fn lemma_assign_maintains_post_att(t: NTrail, f: Formula, lit: Lit) {}

#[trusted] // TMP, todo
#[logic]
#[requires(t.invariant(f))]
#[requires(t.lit_not_in_less(f))]
#[requires(t.lit_is_unique())]
#[requires((@t.trail).len() === 2)]
#[requires((@t.trail).len() > 0)]
#[requires(long_are_post_unit_inner(@t.trail, f, @t.assignments))]
/*
#[requires(forall<i: Int> 0 <= i && i < (@t.trail).len() ==>
     l.idx != (@t.trail)[i].lit.idx
)]
*/
#[requires(forall<i: Int> 0 <= i && i < (@t.trail).len() ==>
    match (@t.trail)[i].reason {
        Reason::Long(k) => !l.lit_in((@f.clauses)[@k]),
        _ => true,
    }
)]
#[ensures(forall<i: Int> 0 <= i && i < (@t.trail).len() ==>
    match (@t.trail)[i].reason {
        Reason::Long(k) => !l.lit_in((@f.clauses)[@k]),
        _ => true,
    }
)]
//)]
//#[requires(forall<i: Int> 0 <= i && i < (@t.trail).len() - 1 ==>
//    !l.lit_in((@f.clauses)[@(@t.trail)[i].lit.idx])
//)]
#[ensures(long_are_post_unit_inner(@t.trail, f, 
(@t.assignments).set(@l.idx, 3u8)))]
//#[ensures(long_are_post_unit_inner((@t.trail).subsequence(0,(@t.trail).len() - 1), f, 
//@t.assignments))]
//#[requires(l === (@t.trail)[(@t.trail).len() - 1].lit)]
fn lemma_pop_maintains_testing(t: NTrail, f: Formula, l: Lit) {
    lemma_assign_maintains_test(f, t.assignments, l)
}

#[logic]
#[requires(a.invariant(f))]
#[requires(f.invariant())]
#[requires(trail_invariant(v, f))]
#[requires(crefs_in_range(v, f))]
#[requires(lit.invariant(@f.num_vars))]
//#[requires(unset((@a)[@lit.idx]))]
#[requires(v.len() === 2)]
#[requires(long_are_post_unit_inner(v, f, @a))]
/*
#[requires(forall<i: Int> 0 <= i && i < v.len() ==>
    match v[i].reason {
        Reason::Long(k) => !lit.lit_in((@f.clauses)[@k]),
        _ => true,
    }
)]
*/
#[requires(forall<i: Int> 0 <= i && i < (@f.clauses).len() && i != cref ==> 
    (@f.clauses)[i].post_unit_inner(@a) ==> 
    (@f.clauses)[i].post_unit_inner((@a).set(@lit.idx, 3u8))
)]
#[requires(forall<i: Int> 0 <= i && i < (@f.clauses).len() && i != cref ==> 
    (!(@f.clauses)[i].post_unit_inner(@a) || !lit.lit_idx_in((@f.clauses)[i]))
)]
/*
#[requires(forall<i: Int> 0 <= i && i < v.len() ==>
    v[i].lit.idx != lit.idx
)]
#[requires(forall<i: Int> 0 <= i && i < v.len() ==>
    !(v[i].lit === lit)
)]
*/
/*
#[requires(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    (@f.clauses)[i].post_unit_inner(@a) !lit.lit_in((@f.clauses)[@k] ==> 
    (@f.clauses)[i].post_unit_inner((@a).set(@lit.idx, 3u8))
)]
*/
/*
#[requires(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    (@f.clauses)[i].post_unit_inner(@a) ==> 
    (@f.clauses)[i].post_unit_inner((@a).set(@lit.idx, 0u8)) 
)]
*/
#[ensures(long_are_post_unit_inner(v, f, (@a).set(@lit.idx, 3u8)))]
//#[ensures(long_are_post_unit_inner(v, f, (@a).set(@lit.idx, 0u8)))]

fn lemma_assign_unwrapped(v: Seq<Step>, f: Formula, a: Assignments, lit: Lit, cref: Int) {}

/*
        forall<j: Int> 0 <= j && j < trail.len() ==> match
        trail[j].reason { 
            Reason::Long(k) => { clause_post_with_regards_to_inner((@f.clauses)[@k], a, j) },
                _ => true,
            }
            */
//#[trusted]
#[logic]
#[requires(t.invariant(f))]
#[requires(t.lit_not_in_less(f))]
#[requires(t.lit_is_unique())]
#[requires((@t.trail).len() === 2)]
#[requires(l === (@t.trail)[(@t.trail).len() - 1].lit)]
#[ensures(forall<i: Int> 0 <= i && i < (@t.trail).len() - 1 ==>
    !l.lit_idx_in((@f.clauses)[@(@t.trail)[i].lit.idx])
)]
fn lemma_last_doesnt_exist_anywhere_else(t: NTrail, f: Formula, l: Lit) {
        t.lit_not_in_less(f);
        t.lit_is_unique();
}

#[trusted]
#[requires(t.invariant(*f))]
#[requires(t.lit_not_in_less(*f))]
#[requires(t.lit_is_unique())]
#[requires((@t.trail).len() > 0)]
//#[requires((@t.trail).len() === 2)]
#[requires(long_are_post_unit_inner(@t.trail, *f, @t.assignments))]
#[ensures(long_are_post_unit_inner((@(^t).trail), *f, 
(@(^t).assignments)))]
fn test_two(t: &mut NTrail, f: &Formula) {
    t.backstep(f);
}

/*
pub fn assign_decision(&mut self, lit: Lit) {
    self.decisions.push(self.steps.len() as LitIdx);
    self.assign(Step {
        assigned_lit: lit,
        decision_level: self.decision_level(),
        reason: Reason::Decision,
    })
}
*/

/*
impl Default for Trail {
    fn default() -> Self {
        Trail {
            assigned: PartialAssignment::default(),
            trail_index: vec![],
            steps: vec![],
            decisions: vec![0],
        }
    }
}
*/

// UNUSED
#[trusted] // OK
#[logic]
#[requires(c.invariant(@f.num_vars))]
//#[requires(a.invariant(f))] // Don't even need this
#[requires(c.post_unit(t.assignments))]
#[ensures(forall<i: Int> 0 <= i && i < (@c).len() ==> !(@c)[i].unset(t.assignments))]
fn lemma_post_unit_no_unset(c: Clause, t: NTrail, f: Formula) {}

#[trusted] // OK
#[logic]
//#[requires(trail_invariant(v, f))]
//#[requires(crefs_in_range(v, f))]
#[requires(a.invariant(f))] 
#[requires(f.invariant())]
#[requires(lit.invariant(@f.num_vars))]
#[requires(unset((@a)[@lit.idx]))]
#[ensures(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    (@f.clauses)[i].post_unit_inner(@a) ==> 
    (@f.clauses)[i].post_unit_inner((@a).set(@lit.idx, 1u8))
)]
#[ensures(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    (@f.clauses)[i].post_unit_inner(@a) ==> 
    (@f.clauses)[i].post_unit_inner((@a).set(@lit.idx, 0u8))
)]
fn lemma_assign_maintains_post_for_each(f: Formula, a: Assignments, lit: Lit) {}

#[trusted] // OK
#[logic]
#[requires(a.invariant(f))]
#[requires(f.invariant())]
#[requires(trail_invariant(v, f))]
#[requires(crefs_in_range(v, f))]
#[requires(lit.invariant(@f.num_vars))]
#[requires(unset((@a)[@lit.idx]))]
#[requires(long_are_post_unit_inner(v, f, @a))]
#[requires(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    (@f.clauses)[i].post_unit_inner(@a) ==> 
    (@f.clauses)[i].post_unit_inner((@a).set(@lit.idx, 1u8))
)]
#[requires(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    (@f.clauses)[i].post_unit_inner(@a) ==> 
    (@f.clauses)[i].post_unit_inner((@a).set(@lit.idx, 0u8)) 
)]
#[ensures(long_are_post_unit_inner(v, f, (@a).set(@lit.idx, 1u8)))]
#[ensures(long_are_post_unit_inner(v, f, (@a).set(@lit.idx, 0u8)))]
fn lemma_assign_maintains_for_each_to_post(v: Seq<Step>, f: Formula, a: Assignments, lit: Lit) {}

#[trusted] // OK
#[logic]
#[requires(a.invariant(f))]
#[requires(f.invariant())]
#[requires(trail_invariant(v, f))]
#[requires(crefs_in_range(v, f))]
#[requires(lit.invariant(@f.num_vars))]
#[requires(unset((@a)[@lit.idx]))]
#[requires(long_are_post_unit_inner(v, f, @a))]
#[ensures(long_are_post_unit_inner(v, f, (@a).set(@lit.idx, 1u8)))]
#[ensures(long_are_post_unit_inner(v, f, (@a).set(@lit.idx, 0u8)))]
pub fn lemma_assign_maintains_long_are_post_unit(v: Seq<Step>, f: Formula, a: Assignments, lit: Lit) {
    lemma_assign_maintains_post_for_each(f, a, lit);
    lemma_assign_maintains_for_each_to_post(v, f, a, lit);
}

#[predicate]
pub fn clause_post_with_regards_to(c: Clause, a: Assignments, j: Int) -> bool {
    pearlite! {
        c.post_unit(a) &&
        exists<i: Int> 0 <= i && i < (@c).len() &&
            @(@c)[i].idx === j &&
            (@c)[i].sat(a) 
    }
}

#[predicate]
pub fn clause_post_with_regards_to_inner(c: Clause, a: Seq<AssignedState>, j: Int) -> bool {
    pearlite! {
        c.post_unit_inner(a) &&
        exists<i: Int> 0 <= i && i < (@c).len() &&
            @(@c)[i].idx === j &&
            (@c)[i].sat_inner(a) 
    }
}

#[predicate]
pub fn long_are_post_unit(trail: NTrail, f: Formula) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < (@trail.trail).len() ==> match
        (@trail.trail)[j].reason { 
            Reason::Long(k) => { clause_post_with_regards_to((@f.clauses)[@k], trail.assignments, j) },
                _ => true,
            }
    }
}

#[predicate]
pub fn long_are_post_unit_inner(trail: Seq<Step>, f: Formula, a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < trail.len() ==> match
        trail[j].reason { 
            Reason::Long(k) => { clause_post_with_regards_to_inner((@f.clauses)[@k], a, j) },
                _ => true,
            }
    }
}