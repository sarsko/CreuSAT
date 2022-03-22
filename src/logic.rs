extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::lit::*;
use crate::clause::*;
use crate::assignments::*;
use crate::formula::*;


// CDCL STUFF START
#[trusted] // OK
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

#[trusted] // OK
#[logic]
#[requires(exists<idx: Int> 0 <= idx && idx < (@a).len() &&
    c3.resolvent_of_idx(c, c2, idx))]
#[requires(!c.sat(a))]
#[requires(!c2.sat(a))]
#[ensures(!c3.sat(a))]
pub fn lemma_sub_clause_not_sat2(c: Clause, c2: Clause, c3: Clause, a: Assignments) {}

// Requires knowledge of the idx of the conflict literal
#[trusted] // OK
#[logic]
#[requires(c3.resolvent_of(c, c2, k, m))]
#[requires(c.sat(a))]
#[requires(c2.sat(a))]
#[ensures(c3.sat(a))]
pub fn lemma_sub_clause_sat(c: Clause, c2: Clause, c3: Clause, a: Assignments, k: Int, m: Int) {}

#[trusted] // OK
#[logic]
#[requires(c.invariant((@a).len()))]
#[requires(c2.invariant((@a).len()))]
#[requires(exists<idx: Int> 0 <= idx && idx < (@a).len() &&
    c3.resolvent_of_idx(c, c2, idx))]
#[requires(c.sat(a))]
#[requires(c2.sat(a))]
#[ensures(c3.sat(a))]
pub fn lemma_sub_clause_sat3(c: Clause, c2: Clause, c3: Clause, a: Assignments) {}

#[trusted] // OK
#[logic]
#[requires(c.invariant((@a).len()))]
#[requires(c2.invariant((@a).len()))]
#[requires(c3.resolvent_of_idx(c, c2, idx))]
#[requires(c.sat(a))]
#[requires(c2.sat(a))]
#[ensures(c3.sat(a))]
pub fn lemma_sub_clause_sat2(c: Clause, c2: Clause, c3: Clause, a: Assignments, idx: Int) {}

#[trusted] // OK
#[logic]
//#[ensures(formula_invariant(f2))]
//#[ensures(f.1 === f2.1)]
#[requires(f2.0 === f.0.push(c))]
#[requires(formula_invariant(f))]
#[ensures((f.0).len() + 1 === (f2.0).len())]
#[ensures(forall<i: Int> 0 <= i && i < (f.0).len() ==> ((f.0)[i]).equals((f2.0)[i]))]
#[ensures(@(f2.0)[(f2.0).len()-1] === @c)]
pub fn lemma_eq_formulas(f: (Seq<Clause>, Int), f2: (Seq<Clause>, Int), c: Clause) {}

//#[trusted] // OK
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(c2.in_formula_inner(f))]
#[requires(c3.resolvent_of(c, c2, k, m))]
#[requires(eventually_sat_complete_no_ass(f))]
#[ensures(eventually_sat_complete_no_ass(((f.0).push(c3), f.1)))]
pub fn lemma_sat_gives_sat(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, k: Int, m: Int) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
}

#[trusted] // OK
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(c2.in_formula_inner(f))]
#[requires(c3.resolvent_of_idx(c, c2, idx))]
#[requires(formula_sat_inner(f, @a))]
#[ensures(formula_sat_inner((f.0.push(c3), f.1), @a))]
pub fn lemma_sat_gives_sat2(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, idx: Int, a: Assignments) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    lemma_sub_clause_not_sat2(c, c2, c3, a);
    lemma_sub_clause_sat2(c, c2, c3, a, idx);
}

#[trusted] // OK
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(c2.in_formula_inner(f))]
#[requires(c3.resolvent_of_idx2(c, c2, idx, c_idx))]
#[requires(formula_sat_inner(f, @a))]
#[ensures(formula_sat_inner((f.0.push(c3), f.1), @a))]
pub fn lemma_sat_gives_sat3(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, idx: Int, c_idx: Int, a: Assignments) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    lemma_sub_clause_not_sat2(c, c2, c3, a);
    lemma_sub_clause_sat2(c, c2, c3, a, idx);
}

#[trusted] // OK
#[logic]
//#[requires(c.in_formula_inner(f))]
//#[requires(c2.in_formula_inner(f))]
//#[requires(c3.resolvent_of(c, c2, k, m))]
#[requires(formula_invariant(f))]
#[requires(!eventually_sat_complete_no_ass(f))]
#[ensures(!eventually_sat_complete_no_ass(((f.0).push(c3), f.1)))]
//#[requires(!formula_sat_inner(f, @a))]
//#[ensures(!formula_sat_inner((f.0.push(c3), f.1), @a))]
pub fn lemma_not_sat_gives_not_sat(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, k: Int, m: Int) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    //lemma_sub_clause_not_sat(c, c2, c3, a);
    //lemma_sub_clause_sat(c, c2, c3, a, k, m);
}

#[trusted] // OK
#[logic]
//#[requires(c.in_formula_inner(f))]
//#[requires(c2.in_formula_inner(f))]
//#[requires(c3.resolvent_of(c, c2, k, m))]
#[requires(formula_invariant(f))]
#[requires(!formula_sat_inner(f, @a))]
#[ensures(!formula_sat_inner((f.0.push(c3), f.1), @a))]
pub fn lemma_not_sat_gives_not_sat2(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, idx: Int, a: Assignments) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    lemma_sub_clause_not_sat2(c, c2, c3, a);
    lemma_sub_clause_sat2(c, c2, c3, a, idx);
}

#[trusted] // OK
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(c2.in_formula_inner(f))]
#[requires(c3.resolvent_of(c, c2, k, m))]
//#[ensures(equisat_compatible_inner(f, (f.0.push(c3), f.1)))]
#[ensures(equisat_extension_inner(c3, f))] 
pub fn lemma_extended_formula_is_equisat_compatible(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, k: Int, m: Int) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    lemma_not_sat_gives_not_sat(f, c, c2, c3, k, m);
    lemma_sat_gives_sat(f, c, c2, c3, k, m);
}

#[trusted] // OK
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(c2.in_formula_inner(f))]
#[requires(c3.resolvent_of_idx2(c, c2, idx, c_idx))]
//#[ensures(equisat_compatible_inner(f, (f.0.push(c3), f.1)))]
#[ensures(equisat_extension_inner(c3, f))] 
pub fn lemma_extended_formula_is_equisat_compatible_new(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, idx: Int, c_idx: Int, a: Assignments) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    lemma_not_sat_gives_not_sat2(f, c, c2, c3, idx, a);
    lemma_sat_gives_sat2(f, c, c2, c3, idx, a);
}

#[trusted] // OK
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(c2.in_formula_inner(f))]
#[requires(c3.resolvent_of_idx(c, c2, idx))]
//#[ensures(equisat_compatible_inner(f, (f.0.push(c3), f.1)))]
#[ensures(equisat_extension_inner(c3, f))] 
pub fn lemma_extended_formula_is_equisat_compatible2(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, idx: Int, a: Assignments) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    lemma_not_sat_gives_not_sat2(f, c, c2, c3, idx, a);
    lemma_sat_gives_sat2(f, c, c2, c3, idx, a);
}

#[trusted] // OK
// Dont think Ill need
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(c2.in_formula_inner(f))]
#[requires(c4.in_formula_inner(f))]
#[requires(c3.resolvent_of(c, c2, k, m))]
#[requires(c5.resolvent_of(c4, c3, kk, mm))]
#[ensures(equisat_extension_inner(c5, f))] 
//#[ensures(equisat_compatible_inner(f, (f.0.push(c5), f.1)))]
pub fn lemma_extended_formula_is_equisat_compatible2_unused(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, c4: Clause, c5: Clause, k: Int, m: Int, kk: Int, mm: Int, a: Assignments) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    lemma_not_sat_gives_not_sat(f, c, c2, c3, k, m);
    lemma_sat_gives_sat(f, c, c2, c3, k, m);
    lemma_extended_formula_is_equisat_compatible(f, c, c2, c3, k, m);
}

#[trusted]
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(equisat_extension_inner(c2, f))]
#[requires(c3.resolvent_of_idx2(c, c2, idx, c_idx))]
#[ensures(equisat_extension_inner(c3, f))]
//#[ensures(equisat_compatible_inner(f, (f.0.push(c3), f.1)))]
pub fn lemma_resolvent_of_equisat_extension_is_equisat_new(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, idx: Int, c_idx: Int, a: Assignments) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    lemma_not_sat_gives_not_sat2(f, c, c2, c3, idx, a);
    lemma_sat_gives_sat3(f, c, c2, c3, idx, c_idx, a);
    lemma_extended_formula_is_equisat_compatible_new(f, c, c2, c3, idx, c_idx, a);
}

//#[trusted] // OK
#[logic]
#[requires(formula_invariant(f))]
#[requires(equisat_extension_inner(c, f))]
#[requires(c2.in_formula_inner(f))]
#[requires(c3.resolvent_of(c, c2, k, m))]
#[ensures(equisat_extension_inner(c3, f))]
//#[ensures(equisat_compatible_inner(f, (f.0.push(c3), f.1)))]
pub fn lemma_resolvent_of_equisat_extension_is_equisat(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, k: Int, m: Int) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    lemma_not_sat_gives_not_sat(f, c, c2, c3, k, m);
    lemma_sat_gives_sat(f, c, c2, c3, k, m);
    lemma_extended_formula_is_equisat_compatible(f, c, c2, c3, k, m);
}

/*
#[logic]
#[requires(formula_invariant(f))]
#[requires(equisat_extension_inner(c, f))]
#[requires(equisat_extension_inner(c2, f))]
#[requires(c3.resolvent_of(c, c2, k, m))]
#[ensures(equisat_extension_inner(c3, f))]
//#[ensures(equisat_compatible_inner(f, (f.0.push(c3), f.1)))]
pub fn lemma_resolvent_of_equisat_extension_is_equisat2(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, k: Int, m: Int, a: Assignments) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    lemma_not_sat_gives_not_sat(f, c, c2, c3, k, m, a);
    lemma_sat_gives_sat(f, c, c2, c3, k, m, a);
    lemma_extended_formula_is_equisat_compatible(f, c, c2, c3, k, m, a);
    lemma_resolvent_of_equisat_extension_is_equisat(f, c, c2, c3, k, m, a);
}
*/

/*
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(equisat_extension_inner(c2, f))]
//#[requires(c3.resolvent_of(c, c2, k, m))]
#[requires(c3.resolvent_of_idx(c, c2, idx))]
#[ensures(equisat_extension_inner(c3, f))]
//#[ensures(equisat_compatible_inner(f, (f.0.push(c3), f.1)))]
pub fn lemma_resolvent_of_equisat_extension_is_equisat4(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, idx: Int, c_index: Int, a: Assignments) {
    lemma_res_idx_to_km(c, c2, c3, idx, a);
    //lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    //lemma_not_sat_gives_not_sat(f, c, c2, c3, k, m, a);
    //lemma_sat_gives_sat(f, c, c2, c3, k, m, a);
    //lemma_extended_formula_is_equisat_compatible(f, c, c2, c3, k, m, a);
}
*/

/*
//#[trusted] // OK
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(equisat_extension_inner(c2, f))]
#[requires(c3.resolvent_of_idx(c, c2, idx))]
#[ensures(equisat_extension_inner(c3, f))]
//#[ensures(equisat_compatible_inner(f, (f.0.push(c3), f.1)))]
pub fn lemma_resolvent_of_equisat_extension_is_equisat_new(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, idx: Int, a: Assignments) {
    lemma_res_idx_to_km(c, c2, c3, idx, a);
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    lemma_not_sat_gives_not_sat(f, c, c2, c3, k, m, a);
    lemma_sat_gives_sat(f, c, c2, c3, k, m, a);
    lemma_extended_formula_is_equisat_compatible2(f, c, c2, c3, idx, a);
}
*/

/*
// Does not prove
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(equisat_extension_inner(c2, f))]
#[requires(c3.resolvent_of_idx(c, c2, idx))]
#[ensures(equisat_extension_inner(c3, f))]
//#[ensures(equisat_compatible_inner(f, (f.0.push(c3), f.1)))]
pub fn lemma_resolvent_of_equisat_extension_is_equisat2(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, idx: Int, a: Assignments) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    lemma_not_sat_gives_not_sat2(f, c, c2, c3, idx, a);
    lemma_sat_gives_sat2(f, c, c2, c3, idx, a);
    lemma_extended_formula_is_equisat_compatible2(f, c, c2, c3, idx, a);
}
*/

#[trusted] // OK
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(c2.in_formula_inner(f))]
#[requires(c3.resolvent_of(c, c2, k, m))]
#[ensures(equisat_extension_inner(c, f))] 
pub fn lemma_resolvent_of_in_is_equisat(f: (Seq<Clause>, Int),  c: Clause, c2: Clause, c3: Clause, k: Int, m: Int, a: Assignments) {
    lemma_extended_formula_is_equisat_compatible(f,  c, c2, c3, k, m);
}


#[trusted] // OK
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(c2.in_formula_inner(f))]
#[requires(c3.resolvent_of_idx(c, c2, idx))]
#[ensures(equisat_extension_inner(c, f))] 
pub fn lemma_resolvent_of_in_is_equisat2(f: (Seq<Clause>, Int),  c: Clause, c2: Clause, c3: Clause, idx: Int, a: Assignments) {
    lemma_extended_formula_is_equisat_compatible2(f,  c, c2, c3, idx, a);
}

#[trusted] // OK
#[logic]
#[requires(formula_invariant(f))]
#[requires(equisat_extension_inner(c, f))] 
#[ensures(equisat_compatible_inner(f, (f.0.push(c), f.1)))]
pub fn lemma_extending_with_equi_ext_is_equi_compat(f: (Seq<Clause>, Int),  c: Clause) {}


#[trusted] // OK
#[logic]
#[requires(f.invariant())]
#[requires(f2.invariant())]
#[requires(f3.invariant())]
#[requires(f.equisat_compatible(f2))]
#[requires(f2.equisat_compatible(f3))]
#[ensures(f.equisat_compatible(f3))]
pub fn lemma_equisat_is_trans(f: Formula, f2: Formula, f3: Formula) {}

//#[trusted]
/*
#[logic]
#[requires(c.invariant((@a).len()))]
#[requires(c2.invariant((@a).len()))]
#[requires(c3.resolvent_of(c, c2, k, m))]
#[ensures(c3.resolvent_of_idx(c, c2, @(@c2)[k].idx))]
pub fn lemma_res_km_idx(c: Clause, c2: Clause, c3: Clause, k: Int, m: Int, a: Assignments) {}
*/

// Slow, but should be easy to make faster
#[trusted] // OK
#[logic]
#[requires(c.invariant((@a).len()))]
#[requires(c2.invariant((@a).len()))]
#[requires(c3.resolvent_of_idx(c, c2, idx))]
#[ensures(exists<k: Int, m: Int> c3.resolvent_of(c, c2, k, m))]
pub fn lemma_res_idx_to_km(c: Clause, c2: Clause, c3: Clause, idx: Int, a: Assignments) {}




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
