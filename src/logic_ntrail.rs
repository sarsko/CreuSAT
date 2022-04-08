extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::lit::*;
use crate::assignments::*;
use crate::formula::*;
use crate::clause::*;
//use crate::logic::*;
use crate::util::*;
use crate::ntrail::*;

#[cfg(contracts)]
use crate::logic::{
    logic_clause::*,
    logic::*,
};


#[predicate]
pub fn crefs_in_range(trail: Seq<Step>, f: Formula) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < trail.len() ==>
            trail[i].invariant(f)
    }
}

#[predicate]
pub fn trail_invariant(trail: Seq<Step>, f: Formula) -> bool {
    pearlite! {
        trail.len() <= @f.num_vars &&
        crefs_in_range(trail, f)
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
pub fn long_are_post_unit(trail: NTrail, f: Formula) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < (@trail.trail).len() ==> match
        (@trail.trail)[j].reason { 
            Reason::Long(k) => { clause_post_with_regards_to((@f.clauses)[@k], trail.assignments, @(@trail.trail)[j].lit.idx) },
                _ => true,
            }
    }
}

#[predicate]
pub fn long_are_post_unit_inner(trail: Seq<Step>, f: Formula, a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < trail.len() ==> match
        trail[j].reason { 
            Reason::Long(k) => { clause_post_with_regards_to_inner((@f.clauses)[@k], a, @(trail)[j].lit.idx) },
                _ => true,
            }
    }
}

#[predicate]
pub fn long_are_post_unit_inner_new(trail: Seq<Step>, f: Formula, a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < trail.len() ==> match
        trail[j].reason { 
            Reason::Long(k) => { clause_post_with_regards_to_inner((@f.clauses)[@k], a, @(trail)[j].lit.idx) },
                _ => true,
            }
    }
}


#[trusted] // OK
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
fn lemma_trail_post(f: Formula, lit: Lit, t: NTrail) {}


#[trusted] // OK
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
fn lemma_trail_only_last(f: Formula, lit: Lit, t: NTrail) {}

// OK well I guess this approach should work
// Just gotta combine this with the pop lemma and then
// Prove the invariants everywhere lol
#[trusted] // OK
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
fn lemma_trail_fin(t: NTrail, f: Formula, lit: Lit) {
    lemma_trail_post(f, lit, t);
    lemma_trail_only_last(f, lit, t);
}

// Checks out, but takes a surprising amount of time
#[trusted] // OK
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
#[requires(long_are_post_unit_inner(@t.trail, f, @t.assignments))]
#[ensures(long_are_post_unit_inner(pop(@t.trail), f, (@t.assignments).set(@lit.idx, 3u8)))]
fn lemma_trail_fin2(t: NTrail, f: Formula, lit: Lit) {
    lemma_trail_post(f, lit, t);
    lemma_trail_only_last(f, lit, t);
}

#[trusted] // Dunno why this isnt checking out
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
fn lemma_trail_fin3(t: NTrail, f: Formula, lit: Lit) {
    //lemma_trail_post(f, lit, t);
    //lemma_trail_only_last(f, lit, t);
    lemma_trail_fin(t, f, lit);
    lemma_trail_fin2(t, f, lit);
}

// OK to pop, but need to fix wipe. 
#[trusted] // OK
#[logic]
#[requires(t.invariant(f))]
#[requires(t.lit_not_in_less(f))]
#[requires(t.lit_is_unique())]
#[requires((@t.trail).len() > 0)]
#[requires(l === (@t.trail)[(@t.trail).len() - 1].lit)]
#[requires(long_are_post_unit_inner(@t.trail, f, @t.assignments))]
#[ensures(long_are_post_unit_inner(pop(@t.trail), f, @t.assignments))]
fn lemma_pop_no_unass_is_ok(t: NTrail, f: Formula, l: Lit) {
}

#[trusted] //OK
#[logic]
#[requires(f.invariant())]
#[requires(t.invariant(f))]
#[requires(t.lit_not_in_less(f))]
#[requires(t.lit_is_unique())]
#[requires((@t.trail).len() > 0)]
#[requires(l.invariant(@f.num_vars))]
#[requires(l === (@t.trail)[(@t.trail).len() - 1].lit)]
#[requires(long_are_post_unit_inner(@t.trail, f, @t.assignments))]
#[ensures(long_are_post_unit_inner(pop(@t.trail), f, 
(@t.assignments).set(@l.idx, 3u8)))]
pub fn lemma_backtrack_ok(t: NTrail, f: Formula, l: Lit) {
    lemma_pop_no_unass_is_ok(t, f, l);
    lemma_trail_fin(t, f, l);
    lemma_trail_fin2(t, f, l);
}


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