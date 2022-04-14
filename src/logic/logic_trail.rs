extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::{
    lit::*,
    assignments::*,
    formula::*,
    clause::*,
    trail::*,
};

#[cfg(contracts)]
use crate::logic::{
    logic_clause::*,
    logic::*,
    logic_util::*,
};

impl Reason {
    #[predicate]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            match self {
                Reason::Long(i) => 
                    (0 <= @i && @i < (@f.clauses).len())
                    && (@(@f.clauses)[@i]).len() > 1
                ,
                Reason::Unit(i) => 
                    (0 <= @i && @i < (@f.clauses).len())
                    && (@(@f.clauses)[@i]).len() == 1
                ,
                _ => true
            }
        }
    }
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
/*
#[predicate]
pub fn trail_entries_are_assigned_inner(trail: Seq<Step>, a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < trail.len() ==>
                a[@(@trail[j]).lit.idx] === bool_to_assignedstate((@trail[j]).lit.polarity)
    }
}
*/

// LOGIC
impl Trail {
    #[predicate]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            self.invariant_no_decision(f)
            && decisions_invariant(@self.decisions, @self.trail)
            // I am not sure these will be needed
            //trail_entries_are_assigned_inner(@self.trail, @self.assignments) && // added
            //assignments_are_in_trail(@self.trail, @self.assignments) // added
        }
    }

    #[predicate]
    pub fn invariant_no_decision(self, f: Formula) -> bool {
        pearlite! {
            self.assignments.invariant(f) 
            && trail_invariant(@self.trail, f)
            && lit_to_level_invariant(@self.lit_to_level, f)
            // added, watch out
            && self.lit_not_in_less(f)
            && self.lit_is_unique()
            && long_are_post_unit_inner(@self.trail, f, @self.assignments)
            && self.trail_entries_are_assigned() // ADDED
            && self.decisions_are_sorted() // NEW
            && unit_are_sat(@self.trail, f, self.assignments)
            // I am not sure these will be needed
            //trail_entries_are_assigned_inner(@self.trail, @self.assignments) && // added
            //assignments_are_in_trail(@self.trail, @self.assignments) // added
        }
    }

    #[predicate]
    pub fn trail_entries_are_assigned(self) -> bool {
        pearlite! {
            trail_entries_are_assigned_inner(@self.trail, @self.assignments)
        }
    }

    #[predicate]
    pub fn decisions_are_sorted(self) -> bool {
        pearlite! {
            sorted(@self.decisions)
        }
    }

    #[predicate]
    pub fn lit_not_in_less(self, f: Formula) -> bool {
        pearlite! {
            // moved into function. May break stuff
            lit_not_in_less_inner(@self.trail, f)
        }
    }

    // Trail does not contail duplicate idxes
    #[predicate]
    pub fn lit_is_unique(self) -> bool {
        pearlite! {
            lit_is_unique_inner(@self.trail)
        }
    }
}

#[predicate]
pub fn lit_not_in_less_inner(t: Seq<Step>, f: Formula) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < t.len() ==>
            forall<j: Int> 0 <= j && j < i ==>
                match t[j].reason {
                    Reason::Long(cref) => !(t)[i].lit.lit_idx_in((@f.clauses)[@cref]),
                    _ => true,
                }
    }
}

#[predicate]
pub fn trail_invariant(trail: Seq<Step>, f: Formula) -> bool {
    pearlite! {
        //trail.len() <= @f.num_vars && // Is this really needed? // might reintroduce it. If so I'll do a proof in enq_assignments
        crefs_in_range(trail, f)
    }
}

#[predicate]
pub fn decisions_invariant(decisions: Seq<usize>, trail: Seq<Step>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < decisions.len() ==> 
            @decisions[i] <= trail.len()
        // Might want to add some semantics? Or nah?
    }
}


#[predicate]
pub fn lit_to_level_invariant(lit_to_level: Seq<usize>, f: Formula) -> bool {
    pearlite! {
        lit_to_level.len() === @f.num_vars
        // Might want to add some semantics? Or nah?
    }
}

#[predicate]
//#[ensures(result === (forall<i: Int> 0 <= i && i < trail.len() ==> trail[i].invariant(f)))]
pub fn crefs_in_range(trail: Seq<Step>, f: Formula) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < trail.len() ==>
            trail[i].invariant(f)
    }
}


#[predicate]
pub fn trail_entries_are_assigned_inner(t: Seq<Step>, a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < t.len() ==>
            //a[@t[j].lit.idx] === bool_to_assignedstate(t[j].lit.polarity)
            t[j].lit.sat_inner(a) // Should be equivalent
    }
}

#[predicate]
pub fn assignments_are_in_trail(t: Seq<Step>, a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < a.len() ==>
            exists<i: Int> 0 <= i && i < t.len() &&
                @t[i].lit.idx == j &&
                bool_to_assignedstate(t[i].lit.polarity) === a[j]
    }
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
pub fn clause_post_with_regards_to_lit(c: Clause, a: Assignments, lit: Lit) -> bool {
    pearlite! {
        c.post_unit(a) &&
        exists<i: Int> 0 <= i && i < (@c).len() &&
            (@c)[i].polarity === lit.polarity &&
            @(@c)[i].idx === @lit.idx &&
            (@c)[i].sat(a) 
    }
}

#[predicate]
pub fn lit_is_unique_inner(trail: Seq<Step>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < trail.len() ==>
            forall<j: Int> 0 <= j && j < i ==>
                trail[j].lit.idx != trail[i].lit.idx
    }
}

#[predicate]
pub fn long_are_post_unit(trail: Trail, f: Formula) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < (@trail.trail).len() ==> 
        match (@trail.trail)[j].reason { 
            Reason::Long(k) => { clause_post_with_regards_to((@f.clauses)[@k], trail.assignments, @(@trail.trail)[j].lit.idx) },
                _ => true,
            }
    }
}

#[predicate]
pub fn long_are_post_unit_inner(trail: Seq<Step>, f: Formula, a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < trail.len() ==> 
            match trail[j].reason { 
                Reason::Long(k) => { clause_post_with_regards_to_inner((@f.clauses)[@k], a, @(trail)[j].lit.idx) },
                    _ => true,
                }
    }
}

#[predicate]
pub fn unit_are_sat(trail: Seq<Step>, f: Formula, a: Assignments) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < trail.len() ==> 
            match trail[j].reason { 
                Reason::Unit(k) => { 
                    trail[j].lit === (@(@f.clauses)[@k])[0]
                    && (@(@f.clauses)[@k])[0].sat(a) },
                    _ => true,
                }
    }
}

#[cfg_attr(all(any(trust_trail, trust_all, trust_logic), all(not(untrust_all), not(untrust_all_logic))), trusted)]
#[logic]
#[requires(f.invariant())]
#[requires(lit.invariant(@f.num_vars))]
#[requires(t.invariant(f))]
#[ensures(forall<i: Int> 0 <= i && i < (@t.trail).len() ==> 
match (@t.trail)[i].reason {
    Reason::Long(k) => ((@f.clauses)[@k].post_unit_inner(@t.assignments) && !lit.lit_idx_in((@f.clauses)[@k])) ==> 
                (@f.clauses)[@k].post_unit_inner((@t.assignments).set(@lit.idx, 3u8)),
    _ => true,
}
)]
#[ensures(forall<i: Int> 0 <= i && i < (@t.trail).len() ==> 
match (@t.trail)[i].reason {
    Reason::Long(k) => ((@f.clauses)[@k].post_unit_inner(@t.assignments) && !lit.lit_idx_in((@f.clauses)[@k])) ==> 
                (@f.clauses)[@k].post_unit_inner((@t.assignments).set(@lit.idx, 2u8)),
    _ => true,
}
)]
fn lemma_trail_post(f: Formula, lit: Lit, t: Trail) {}


#[cfg_attr(all(any(trust_trail, trust_all, trust_logic), all(not(untrust_all), not(untrust_all_logic))), trusted)]
#[logic]
#[requires(t.invariant(f))]
#[requires(f.invariant())]
#[requires(t.lit_not_in_less(f))]
#[requires(t.lit_is_unique())]
#[requires(lit.invariant(@f.num_vars))]
#[requires((@t.trail).len() > 0)]
#[requires(lit === (@t.trail)[(@t.trail).len() - 1].lit)]
#[ensures(forall<i: Int> 0 <= i && i < (@t.trail).len() - 1 ==> 
    match (@t.trail)[i].reason {
        Reason::Long(k) => !lit.lit_idx_in((@f.clauses)[@k]),
        _ => true,
    }
)]
fn lemma_trail_only_last(f: Formula, lit: Lit, t: Trail) {}

// OK well I guess this approach should work
// Just gotta combine this with the pop lemma and then
// Prove the invariants everywhere lol
#[cfg_attr(all(any(trust_trail, trust_all, trust_logic), all(not(untrust_all), not(untrust_all_logic))), trusted)]
#[logic]
#[requires(f.invariant())]
#[requires(t.lit_not_in_less(f))]
#[requires(t.lit_is_unique())]
#[requires(lit.invariant(@f.num_vars))]
#[requires((@t.trail).len() > 0)]
#[requires(t.invariant(f))]
#[requires(lit === (@t.trail)[(@t.trail).len() - 1].lit)]
#[ensures(forall<i: Int> 0 <= i && i < (@t.trail).len() - 1 ==> 
    match (@t.trail)[i].reason {
        Reason::Long(k) => (@f.clauses)[@k].post_unit_inner(@t.assignments) ==> 
                (@f.clauses)[@k].post_unit_inner((@t.assignments).set(@lit.idx, 3u8)),
        _ => true,
    }
)]
#[ensures(forall<i: Int> 0 <= i && i < (@t.trail).len() - 1 ==> 
    match (@t.trail)[i].reason {
        Reason::Long(k) => (@f.clauses)[@k].post_unit_inner(@t.assignments) ==> 
                (@f.clauses)[@k].post_unit_inner((@t.assignments).set(@lit.idx, 2u8)),
        _ => true,
    }
)]
fn lemma_trail_fin(t: Trail, f: Formula, lit: Lit) {
    lemma_trail_post(f, lit, t);
    lemma_trail_only_last(f, lit, t);
}

// Checks out, but takes a surprising amount of time
#[cfg_attr(all(any(trust_trail, trust_all, trust_logic), all(not(untrust_all), not(untrust_all_logic))), trusted)]
#[logic]
#[requires(f.invariant())]
#[requires(t.invariant(f))]
#[requires(t.lit_not_in_less(f))]
#[requires(t.lit_is_unique())]
#[requires(lit.invariant(@f.num_vars))]
#[requires((@t.trail).len() > 0)]
#[requires(lit === (@t.trail)[(@t.trail).len() - 1].lit)]
#[requires(forall<i: Int> 0 <= i && i < (@t.trail).len() - 1 ==> 
    match (@t.trail)[i].reason {
        Reason::Long(k) => (@f.clauses)[@k].post_unit_inner(@t.assignments) ==> 
                (@f.clauses)[@k].post_unit_inner((@t.assignments).set(@lit.idx, 3u8)),
        _ => true,
    }
)]
#[requires(forall<i: Int> 0 <= i && i < (@t.trail).len() - 1 ==> 
    match (@t.trail)[i].reason {
        Reason::Long(k) => (@f.clauses)[@k].post_unit_inner(@t.assignments) ==> 
                (@f.clauses)[@k].post_unit_inner((@t.assignments).set(@lit.idx, 2u8)),
        _ => true,
    }
)]
#[requires(long_are_post_unit_inner(@t.trail, f, @t.assignments))]
#[ensures(long_are_post_unit_inner(pop(@t.trail), f, (@t.assignments).set(@lit.idx, 2u8)))]
#[ensures(long_are_post_unit_inner(pop(@t.trail), f, (@t.assignments).set(@lit.idx, 3u8)))]
fn lemma_trail_fin2(t: Trail, f: Formula, lit: Lit) {
    lemma_trail_post(f, lit, t);
    lemma_trail_only_last(f, lit, t);
}

#[cfg_attr(all(any(trust_trail, trust_all, trust_logic), all(not(untrust_all), not(untrust_all_logic))), trusted)]
#[logic]
#[requires(f.invariant())]
#[requires(t.invariant(f))]
#[requires(t.lit_not_in_less(f))]
#[requires(t.lit_is_unique())]
#[requires(lit.invariant(@f.num_vars))]
#[requires((@t.trail).len() > 0)]
#[requires(lit === (@t.trail)[(@t.trail).len() - 1].lit)]
#[requires(long_are_post_unit_inner(@t.trail, f, @t.assignments))]
#[ensures(long_are_post_unit_inner(pop(@t.trail), f, (@t.assignments).set(@lit.idx, 3u8)))]
#[ensures(long_are_post_unit_inner(pop(@t.trail), f, (@t.assignments).set(@lit.idx, 2u8)))]
fn lemma_trail_fin3(t: Trail, f: Formula, lit: Lit) {
    //lemma_trail_post(f, lit, t);
    //lemma_trail_only_last(f, lit, t);
    lemma_trail_fin(t, f, lit);
    lemma_trail_fin2(t, f, lit);
}

// OK to pop, but need to fix wipe. 
//#[cfg_attr(all(any(trust_trail, trust_all, trust_logic), all(not(untrust_all), not(untrust_all_logic))), trusted)]
#[cfg_attr(all(any(trust_trail, trust_all, trust_logic), all(not(untrust_all), not(untrust_all_logic))), trusted)]
#[logic]
#[requires(t.invariant(f))]
#[requires(t.lit_not_in_less(f))]
#[requires(t.lit_is_unique())]
#[requires((@t.trail).len() > 0)]
#[requires(l === (@t.trail)[(@t.trail).len() - 1].lit)]
#[requires(long_are_post_unit_inner(@t.trail, f, @t.assignments))]
#[ensures(long_are_post_unit_inner(pop(@t.trail), f, @t.assignments))]
fn lemma_pop_no_unass_is_ok(t: Trail, f: Formula, l: Lit) {}

//#[cfg_attr(all(any(trust_trail, trust_all, trust_logic), all(not(untrust_all), not(untrust_all_logic))), trusted)]
#[cfg_attr(all(any(trust_trail, trust_all, trust_logic), all(not(untrust_all), not(untrust_all_logic))), trusted)]
#[logic]
#[requires(f.invariant())]
#[requires(t.invariant(f))]
#[requires(t.lit_not_in_less(f))]
#[requires(t.lit_is_unique())]
#[requires((@t.trail).len() > 0)]
#[requires(l.invariant(@f.num_vars))]
#[requires(l === (@t.trail)[(@t.trail).len() - 1].lit)]
#[requires(long_are_post_unit_inner(@t.trail, f, @t.assignments))]
#[ensures(long_are_post_unit_inner(pop(@t.trail), f, (@t.assignments).set(@l.idx, 3u8)))]
#[ensures(long_are_post_unit_inner(pop(@t.trail), f, (@t.assignments).set(@l.idx, 2u8)))]
pub fn lemma_backtrack_ok(t: Trail, f: Formula, l: Lit) {
    lemma_pop_no_unass_is_ok(t, f, l);
    lemma_trail_fin(t, f, l);
    lemma_trail_fin2(t, f, l);
}


// UNUSED

#[cfg_attr(all(any(trust_trail, trust_all, trust_logic), not(untrust_all)), trusted)]
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

#[cfg_attr(all(any(trust_trail, trust_all, trust_logic), not(untrust_all)), trusted)]
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

#[cfg_attr(all(any(trust_trail, trust_all, trust_logic), not(untrust_all)), trusted)]
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

// with lit unwrapped // TODO
#[cfg_attr(all(any(trust_trail, trust_all, trust_logic), not(untrust_all)), trusted)]
#[logic]
#[requires(a.invariant(f))]
#[requires(f.invariant())]
#[requires(trail_invariant(v, f))]
#[requires(crefs_in_range(v, f))]
#[requires(@idx < @f.num_vars)]
#[requires(unset((@a)[@idx]))]
#[requires(long_are_post_unit_inner(v, f, @a))]
#[ensures(long_are_post_unit_inner(v, f, (@a).set(@idx, 1u8)))]
#[ensures(long_are_post_unit_inner(v, f, (@a).set(@idx, 0u8)))]
pub fn lemma_assign_maintains_long_are_post_unit2(v: Seq<Step>, f: Formula, a: Assignments, idx: usize) {
    //lemma_assign_maintains_post_for_each(f, a, idx)
    //lemma_assign_maintains_for_each_to_post(v, f, a, idx);
}

#[cfg_attr(all(any(trust_trail, trust_all, trust_logic), not(untrust_all)), trusted)]
#[logic]
#[requires(c.invariant(@f.num_vars))]
#[requires(c.post_unit(t.assignments))]
#[ensures(forall<i: Int> 0 <= i && i < (@c).len() ==> !(@c)[i].unset(t.assignments))]
fn lemma_post_unit_no_unset(c: Clause, t: Trail, f: Formula) {}

#[cfg_attr(all(any(trust_trail, trust_all, trust_logic), not(untrust_all)), trusted)]
#[logic]
#[requires(c.invariant(@f.num_vars))]
#[requires(c.post_unit(t.assignments))]
#[requires(idx < @f.num_vars)]
#[requires(unset((@t.assignments)[idx]))]
#[ensures(forall<i: Int> 0 <= i && i < (@c).len() ==> @(@c)[i].idx != idx)]
fn lemma_idx_not_in_post_unit(c: Clause, t: Trail, f: Formula, idx: Int) {}

#[cfg_attr(all(any(trust_trail, trust_all, trust_logic), not(untrust_all)), trusted)]
#[logic]
//#[requires(f.invariant())]
#[requires(t.invariant(f))]
#[requires(step.invariant(f))]
#[requires(unset((@t.assignments)[@step.lit.idx]))]
#[ensures(forall<i: Int> 0 <= i && i < (@t.trail).len() ==>
    match (@t.trail)[i].reason {
        Reason::Long(cref) => 
        forall<k: Int> 0 <= k && k < (@(@f.clauses)[@cref]).len() ==> 
            (@(@f.clauses)[@cref])[k].idx != step.lit.idx,
        _ => true,
})]
fn lemma_unset_to_forall(t: Trail, f: Formula, step: Step) {}

#[cfg_attr(all(any(trust_trail, trust_all, trust_logic), not(untrust_all)), trusted)]
#[logic]
//#[requires(f.invariant())]
#[requires(t.invariant(f))]
#[requires(unset((@t.assignments)[@step.lit.idx]))]
#[requires(step.invariant(f))]
#[requires(forall<i: Int> 0 <= i && i < (@t.trail).len() ==>
    match (@t.trail)[i].reason {
        Reason::Long(cref) => 
            forall<k: Int> 0 <= k && k < (@(@f.clauses)[@cref]).len() ==> 
                (@(@f.clauses)[@cref])[k].idx != step.lit.idx,
            _ => true,
})]
#[ensures(lit_not_in_less_inner((@t.trail).push(step), f))]
fn lemma_forall_to_unset_push(t: Trail, f: Formula, step: Step) {}

#[cfg_attr(all(any(trust_trail, trust_all, trust_logic), not(untrust_all)), trusted)]
#[logic]
#[requires(f.invariant())]
#[requires(t.invariant(f))]
#[requires(unset((@t.assignments)[@step.lit.idx]))]
#[requires(step.invariant(f))]
#[requires(lit_not_in_less_inner(@t.trail, f))]
#[ensures(lit_not_in_less_inner((@t.trail).push(step), f))]
pub fn lemma_push_maintains_lit_not_in_less(t: Trail, f: Formula, step: Step) {
        lemma_unset_to_forall(t, f, step);
        lemma_forall_to_unset_push(t, f, step);
}