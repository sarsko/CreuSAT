extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::lit::*;
use crate::clause::*;
use crate::assignments::*;
use crate::formula::*;


// CDCL STUFF START
#[predicate]
pub fn resolvent_of_(c3: Clause, c: Clause, c2: Clause, idx: usize) -> bool{
    pearlite! {
         forall<i: Int> 0 <= i && i < (@c ).len() && !(@(@c)[i].idx === @idx) ==> (@c )[i].lit_in(c3) &&
         forall<i: Int> 0 <= i && i < (@c2).len() && !(@(@c)[i].idx === @idx) ==> (@c2)[i].lit_in(c3) &&
        (forall<i: Int> 0 <= i && i < (@c3).len()           ==> (@c3)[i].lit_in(c) 
                                                            ||  (@c3)[i].lit_in(c2))
    }
}


#[trusted] // OK
#[logic]
#[requires(f.invariant())]
#[requires(f2.invariant())]
#[requires(f.equisat_compatible(f2))]
#[requires(f.eventually_sat_complete_no_ass())]
#[ensures(f2.eventually_sat_complete_no_ass())]
pub fn lemma_trivial(f: Formula, f2: Formula) {}

// Trivial
// De facto test
#[trusted] // OK
#[logic]
#[requires(f.invariant())]
#[requires(f2.invariant())]
#[requires(f === f2)]
#[ensures(f.equisat_compatible(f2))]
pub fn lemma_equal_are_equisat(f: Formula, f2: Formula) {}

// Trivial
// De facto test
#[trusted] // OK
#[logic]
#[requires(f.invariant())]
#[requires(f2.invariant())]
#[requires(@f.num_vars === @f2.num_vars)]
#[requires((@f.clauses).len() === (@f2.clauses).len())]
#[requires(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    (@f.clauses)[i] === (@f2.clauses)[i])]
#[ensures(f.equisat_compatible(f2))]
pub fn lemma_equal_are_equisat2(f: Formula, f2: Formula) {}

// Trivial
// De facto test
#[trusted] // OK
#[logic]
#[requires(f.invariant())]
#[requires(f2.invariant())]
#[requires(@f.num_vars === @f2.num_vars)]
#[requires((@f.clauses).len() === (@f2.clauses).len())]
#[requires(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    (@(@f.clauses)[i]).len() === (@(@f2.clauses)[i]).len() &&
    forall<j: Int> 0 <= j && j < (@(@f.clauses)[i]).len() ==>
    (@(@f.clauses)[i])[j] === (@(@f2.clauses)[i])[j]
)]
#[ensures(f.equisat_compatible(f2))]
pub fn lemma_equal_are_equisat3(f: Formula, f2: Formula) {}


//#[trusted] // OK
#[logic]
#[requires(f.invariant())]
#[requires(f2.invariant())]
#[requires(@f.num_vars === @f2.num_vars)]
#[requires((@f.clauses).len() + 1 === (@f2.clauses).len())]
#[requires(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    ((@f.clauses)[i]).equals((@f2.clauses)[i]))]
#[requires(@(@f2.clauses)[(@f2.clauses).len()-1] === @c3)]
#[requires(c.in_formula(f))]
#[requires(c2.in_formula(f))]
#[requires(c3.resolvent_of(c, c2, k, m))]
#[requires(f.sat(a))]
#[ensures(f2.sat(a))]
pub fn lemma_sat_gives_sat(f: Formula, f2: Formula, c: Clause, c2: Clause, c3: Clause, k: Int, m: Int, a: Assignments) {
    lemma_sub_clause_not_sat(c, c2, c3, a);
    lemma_sub_clause_sat(c, c2, c3, a, k, m);
}

//#[trusted] // OK
#[logic]
#[requires(f.invariant())]
#[requires(f2.invariant())]
#[requires(@f.num_vars === @f2.num_vars)]
#[requires((@f.clauses).len() + 1 === (@f2.clauses).len())]
#[requires(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    ((@f.clauses)[i]).equals((@f2.clauses)[i]))]
#[requires(@(@f2.clauses)[(@f2.clauses).len()-1] === @c3)]
#[requires(c.in_formula(f))]
#[requires(c2.in_formula(f))]
#[requires(c3.resolvent_of(c, c2, k, m))]
#[requires(!f.sat(a))]
#[ensures(!f2.sat(a))]
pub fn lemma_not_sat_gives_not_sat(f: Formula, f2: Formula, c: Clause, c2: Clause, c3: Clause, k: Int, m: Int, a: Assignments) {
    lemma_sub_clause_not_sat(c, c2, c3, a);
    lemma_sub_clause_sat(c, c2, c3, a, k, m);
}

//#[trusted] // OK
#[logic]
#[requires(f.invariant())]
#[requires(f2.invariant())]
#[requires(@f.num_vars === @f2.num_vars)]
#[requires((@f.clauses).len() + 1 === (@f2.clauses).len())]
#[requires(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    ((@f.clauses)[i]).equals((@f2.clauses)[i]))]
#[requires(@(@f2.clauses)[(@f2.clauses).len()-1] === @c3)]
#[requires(c.in_formula(f))]
#[requires(c2.in_formula(f))]
#[requires(c3.resolvent_of(c, c2, k, m))]
#[ensures(f.equisat_compatible(f2))]
#[ensures(c3.equisat_extension(f, f2))] // OK
pub fn lemma_extended_formula_is_equisat_compatible(f: Formula, f2: Formula, c: Clause, c2: Clause, c3: Clause, k: Int, m: Int, a: Assignments) {
    lemma_not_sat_gives_not_sat(f, f2, c, c2, c3, k, m, a);
    lemma_sat_gives_sat(f, f2, c, c2, c3, k, m, a);
}

//#[trusted] // OK
#[logic]
#[requires(forall<i: Int> 0 <= i && i < (@c ).len() ==> (@c )[i].lit_in(c3) ||
    (exists<j: Int> 0 <= j && j < (@c2).len() && (@c )[i].is_opp((@c2)[j])))]
#[requires(forall<i: Int> 0 <= i && i < (@c2).len() ==> (@c2)[i].lit_in(c3) ||
    (exists<j: Int> 0 <= j && j < (@c ).len() && (@c2)[i].is_opp((@c)[j])))]
#[requires(forall<i: Int> 0 <= i && i < (@c3).len() ==> (@c3)[i].lit_in(c) 
                                                     || (@c3)[i].lit_in(c2))]
#[requires(!c.sat(a))]
#[requires(!c2.sat(a))]
#[ensures(!c3.sat(a))]
pub fn lemma_sub_clause_not_sat(c: Clause, c2: Clause, c3: Clause, a: Assignments) {}

// Requires knowledge of the idx of the conflict literal
//#[trusted] // OK
#[logic]
#[requires(c3.resolvent_of(c, c2, k, m))]
#[requires(c.sat(a))]
#[requires(c2.sat(a))]
#[ensures(c3.sat(a))]
pub fn lemma_sub_clause_sat(c: Clause, c2: Clause, c3: Clause, a: Assignments, k: Int, m: Int) {}

// CDCL STUFF END


#[trusted] // OK
#[logic]
#[ensures(b ==> @result === 1)]
#[ensures(!b ==> @result === 0)]
pub fn bool_to_assignedstate(b: bool) -> AssignedState {
    if b {
        1u8
    } else {
        0u8
    }
}

#[logic]
fn flip_v(v: AssignedState) -> AssignedState {
    pearlite! {
        if @v === 0 {
            1u8
        } else if @v === 1 {
            0u8
        } else {
            v
        }
    }
}

#[logic]
fn pos() -> AssignedState {
    1u8
}

#[logic]
fn neg() -> AssignedState {
    0u8
}

#[predicate]
pub fn unset(v: AssignedState) -> bool {
    pearlite! {
        if @v >= 2 {
            true
        } else {
            false
        }
    }
}

#[trusted] // OK
#[logic]
#[requires(f.invariant())]
#[requires(assignments_invariant(a, f))]
#[requires(complete_inner(a))]
#[ensures(f.unsat_inner(a) || f.sat_inner(a))]
pub fn lemma_complete_implies_sat_or_unsat(f: Formula, a: Seq<AssignedState>) {}

#[trusted] // OK
#[logic]
#[requires(f.invariant())]
#[requires(assignments_invariant(a, f))]
#[requires(complete_inner(a))]
#[requires(!f.sat_inner(a))]
#[ensures(f.unsat_inner(a))]
pub fn lemma_complete_and_not_sat_implies_unsat(f: Formula, a: Seq<AssignedState>) {
    lemma_complete_implies_sat_or_unsat(f, a);
}

#[trusted] // OK
#[logic]
#[requires(f.invariant())]
#[requires(assignments_invariant(a, f))]
#[requires(complete_inner(a))]
#[requires(!f.unsat_inner(a))]
#[ensures(f.sat_inner(a))]
pub fn lemma_complete_and_not_unsat_implies_sat(f: Formula, a: Seq<AssignedState>) {
    lemma_complete_implies_sat_or_unsat(f, a);
}

#[trusted] // OK
#[logic] 
#[requires(f.invariant())]
#[requires(assignments_invariant(a, f))]
#[requires(f.unsat_inner(a))]
#[ensures(!f.eventually_sat_complete_inner(a))]
pub fn lemma_not_sat_formula_implies_unsat_formula(f: Formula, a: Seq<AssignedState>) {}

#[trusted] // OK
#[logic]
#[requires(c.unsat_inner(a))]
#[requires(c.in_formula(f))]
#[ensures(f.unsat_inner(a))]
pub fn lemma_not_sat_clause_implies_unsat_formula(f: Formula, c: Clause, a: Seq<AssignedState>) {}


#[trusted] // OK
#[logic]
#[requires(f.invariant())]
#[requires(@f.num_vars === a.len())]
#[requires(0 <= ix && ix < a.len() && unset(a[ix]))]
#[requires(!unset(v))]
#[requires(f.eventually_sat_complete_inner(a))]
#[requires(!f.eventually_sat_complete_inner(a.set(ix, flip_v(v))))]
#[ensures(f.eventually_sat_complete_inner(a.set(ix, v)))]
pub fn lemma_unit_forces(c: Clause, f: Formula, a: Seq<AssignedState>, ix: Int, v: AssignedState) {
    lemma_not_sat_formula_implies_unsat_formula(f, a);
}

#[trusted] // OK
#[logic]
#[requires(f.invariant())]
#[requires(@f.num_vars === a.len())]
#[requires(0 <= ix && ix < a.len() && unset(a[ix]))]
#[requires(!unset(v))]
#[requires(c.unit_inner(a))]
#[requires(c.in_formula(f))]
#[requires(c.invariant(a.len()))]
#[requires(exists<j: Int> 0 <= j && j < (@c).len() && @(@c)[j].idx === ix && bool_to_assignedstate(((@c)[j].polarity)) === v)]
#[requires(forall<j: Int> 0 <= j && j < (@c).len() && !(@(@c)[j].idx === ix) ==> (@c)[j].unsat_inner(a))]
#[ensures(!f.eventually_sat_complete_inner(a.set(ix, flip_v(v))))]
#[ensures(f.unsat_inner(a.set(ix, flip_v(v))))]
pub fn lemma_unit_wrong_polarity_unsat_formula(c: Clause, f: Formula, a: Seq<AssignedState>, ix: Int, v: AssignedState) {
    lemma_not_sat_formula_implies_unsat_formula(f, a);
    lemma_correct_polarity_makes_clause_sat(c, a, ix, v);
    lemma_incorrect_polarity_makes_clause_unsat(c, a, ix, v);
    lemma_not_sat_clause_implies_unsat_formula(f, c, a.set(ix, flip_v(v)));
}

#[trusted] // OK
#[logic]
#[requires(0 <= ix && ix < a.len())]
#[requires(exists<j: Int> 0 <= j && j < (@c).len() && @(@c)[j].idx === ix && bool_to_assignedstate((@c)[j].polarity) === v)]
#[ensures(c.sat_inner(a.set(ix, v)))]
pub fn lemma_correct_polarity_makes_clause_sat(c: Clause, a: Seq<AssignedState>, ix: Int, v: AssignedState) {}

#[trusted] // OK
#[logic]
#[requires(!unset(v))]
#[requires(0 <= ix && ix < a.len() && unset(a[ix]))]
#[requires(c.unit_inner(a))]
#[requires(!c.sat_inner(a))]
#[requires(exists<j: Int> 0 <= j && j < (@c).len() && @(@c)[j].idx === ix && (@c)[j].sat_inner(a) )]
#[requires(c.invariant(a.len()))]
#[requires(forall<j: Int> 0 <= j && j < (@c).len() && !(@(@c)[j].idx === ix) ==> (@c)[j].unsat_inner(a))]
#[ensures(forall<j: Int> 0 <= j && j < (@c).len()  ==> !unset((a.set(ix, v))[@(@c)[j].idx]))]
#[ensures(!(unset(a.set(ix, flip_v(v))[ix])))]
#[ensures(c.unsat_inner(a.set(ix, flip_v(v))))]
#[ensures(!c.sat_inner(a.set(ix, flip_v(v))))]
pub fn lemma_incorrect_polarity_makes_clause_unsat(c: Clause, a: Seq<AssignedState>, ix: Int, v: AssignedState) {}

#[trusted] // OK
#[logic]
#[requires(0 <= ix && ix < a.len() && unset(a[ix]))]
#[requires(f.eventually_sat_complete_inner(a.set(ix, v)))]
#[ensures(f.eventually_sat_complete_inner(a))]
pub fn lemma_extension_sat_base_sat(f: Formula, a: Seq<AssignedState>, ix: Int, v: AssignedState) {}

#[trusted] // OK
#[logic]
#[requires(0 <= ix && ix < a.len() && unset(a[ix]))]
#[requires(!f.eventually_sat_complete_inner(a.set(ix, neg())))]
#[requires(!f.eventually_sat_complete_inner(a.set(ix, pos())))]
#[ensures(!f.eventually_sat_complete_inner(a))]
pub fn lemma_extensions_unsat_base_unsat(a: Seq<AssignedState>, ix: Int, f: Formula) {
    compatible_inner(a, a.set(ix, pos()));
    compatible_inner(a, a.set(ix, neg()));
}
