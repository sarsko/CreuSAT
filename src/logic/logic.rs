extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{assignments::*, clause::*, formula::*, lit::*, trail::*};

use crate::logic::{logic_assignments::*, logic_clause::*, logic_formula::*, logic_trail::*};

// Trail stuff start
/*
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

#[logic]
#[requires(trail_invariant_full_no_sep(t, f))]
#[requires(trail_entries_are_assigned_inner(t.0, a))]
#[requires(long_are_post_unit_inner(t.1, f, a))]
#[requires(t.0.len() > 0)]
//#[requires((@(t.0)[0]).len() > 0)]
#[requires((@last_elem(t.0)).len() > 0)]
#[ensures((@last_elem(t.0)))]
//#[ensures((@(t.0)[0])[(@(t.0)[0]).len()-1])]
pub fn lemma_trail_1(t: (Seq<Vec<Lit>>, Seq<(usize, Reason)>), f: Formula, a: Seq<AssignedState>) {}
*/

/*


*/

// Trail stuff end
// CDCL 2 STUFF START (WIP)
#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(c.sat(a))]
#[requires((@c2).permut(@c, 0, (@c).len()))]
#[ensures(c2.sat(a))]
pub fn lemma_permut_clause_ok(c: Clause, c2: Clause, a: Assignments) {}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(c.unsat(a))]
#[requires((@c2).permut(@c, 0, (@c).len()))]
#[ensures(c2.unsat(a))]
pub fn lemma_permut_clause_ok2(c: Clause, c2: Clause, a: Assignments) {}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires((@c).len() >= 2)]
#[requires((@c2).len() === (@c).len())]
#[requires((@c2).exchange(@c, a, b))]
#[requires(no_duplicate_indexes_inner(@c))]
#[ensures(no_duplicate_indexes_inner(@c2))]
pub fn lemma_swap_clause_no_dups(c: Clause, c2: Clause, a: Int, b: Int) {}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires((@c).len() >= 2)]
#[requires((@c2).len() === (@c).len())]
#[requires((@c2).exchange(@c, a, b))]
#[requires(c.post_unit(ass))]
#[ensures(c2.post_unit(ass))]
pub fn lemma_swap_maintains_post_unit(c: Clause, c2: Clause, a: Int, b: Int, ass: Assignments) {
    lemma_swap_clause_no_dups(c, c2, a, b);
}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires((@c).len() >= 2)]
#[requires((@c2).len() === (@c).len())]
#[requires((@c2).exchange(@c, a, b))]
#[requires(clause_post_with_regards_to(c, ass, j))]
#[ensures(clause_post_with_regards_to(c2, ass, j))]
#[ensures(clause_post_with_regards_to_inner(c2, @ass, j))]
pub fn lemma_swap_maintains_post_with_regards_to(
    c: Clause,
    c2: Clause,
    a: Int,
    b: Int,
    ass: Assignments,
    j: Int,
) {
    lemma_swap_maintains_post_unit(c, c2, a, b, ass);
}

/*
#[logic]
#[requires((@c).len() >= 2)]
#[requires((@c2).len() === (@c).len())]
#[requires((@c2).exchange(@c, a, b))]
#[requires(
    c.post_unit(ass))]
#[ensures(c2.post_unit(ass))]
pub fn lemma_swap_maintains_post_unit(c: Clause, c2: Clause, a: Int, b: Int, ass: Assignments) {
    lemma_swap_clause_no_dups(c, c2, a, b);
}
*/

/*
#[logic]
#[requires(c.invariant(n))]
#[requires((@c2).permut(@c, 0, (@c).len()))]
#[ensures(c2.invariant(n))]
pub fn lemma_permut_clause_invariant(c: Clause, c2: Clause, n: Int) {}
*/

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(f.sat(a))]
#[requires((@f2.clauses).permut(@f.clauses, 0, (@f.clauses).len()))]
#[requires(@f2.num_vars === @f.num_vars)]
#[ensures(f2.sat(a))]
pub fn lemma_permut_formula_ok(f: Formula, f2: Formula, a: Assignments) {}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(f.unsat(a))]
#[requires((@f2.clauses).permut(@f.clauses, 0, (@f.clauses).len()))]
#[requires(@f2.num_vars === @f.num_vars)]
#[ensures(f2.unsat(a))]
pub fn lemma_permut_formula_ok2(f: Formula, f2: Formula, a: Assignments) {}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(f.eventually_sat_complete_no_ass())]
#[requires((@f2.clauses).permut(@f.clauses, 0, (@f.clauses).len()))]
#[requires(@f2.num_vars === @f.num_vars)]
#[ensures(f2.eventually_sat_complete_no_ass())]
pub fn lemma_permut_formula_ok_no_ass(f: Formula, f2: Formula) {}

/*
#[logic]
#[requires(f.eventually_sat_complete_no_ass())]
#[requires((@f2.clauses).len() === (@f.clauses).len())]
#[requires(forall<i: Int> 0 <= i && i < (@f2.clauses).len() ==>
    (@(@f2.clauses)[i]).permut((@(@f.clauses)[i]), 0, (@(@f.clauses)[i]).len()))]
#[requires(@f2.num_vars === @f.num_vars)]
#[ensures(f2.eventually_sat_complete_no_ass())]
pub fn lemma_permut_formula_ok_no_ass2(f: Formula, f2: Formula) {}
*/

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(f.eventually_sat_complete_no_ass())]
#[requires((@f2.clauses).len() === (@f.clauses).len())]
#[requires(forall<i: Int> 0 <= i && i < (@f2.clauses).len() && i != cref ==>
    (@(@f2.clauses)[i]) === (@(@f.clauses)[i]))]
#[requires((@(@f2.clauses)[cref]).permut((@(@f.clauses)[cref]), 0, (@(@f.clauses)[cref]).len()))]
#[requires(@f2.num_vars === @f.num_vars)]
#[ensures(f2.eventually_sat_complete_no_ass())]
pub fn lemma_permut_clause_in_formula_maintains_sat(f: Formula, f2: Formula, cref: Int) {}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(!f.eventually_sat_complete_no_ass())]
#[requires((@f2.clauses).len() === (@f.clauses).len())]
#[requires(forall<i: Int> 0 <= i && i < (@f2.clauses).len() && i != cref ==>
    (@(@f2.clauses)[i]) === (@(@f.clauses)[i]))]
#[requires((@(@f2.clauses)[cref]).permut((@(@f.clauses)[cref]), 0, (@(@f.clauses)[cref]).len()))]
#[requires(@f2.num_vars === @f.num_vars)]
#[ensures(!f2.eventually_sat_complete_no_ass())]
pub fn lemma_permut_clause_in_formula_maintains_unsat(f: Formula, f2: Formula, cref: Int) {}

/*
#[logic]
#[requires(f.invariant())]
#[requires((@f2.clauses).len() === (@f.clauses).len())]
#[requires(forall<i: Int> 0 <= i && i < (@f2.clauses).len() && i != cref ==>
    (@(@f2.clauses)[i]) === (@(@f.clauses)[i]))]
#[requires((@(@f2.clauses)[cref]).permut((@(@f.clauses)[cref]), 0, (@(@f.clauses)[cref]).len()))]
#[requires(@f2.num_vars === @f.num_vars)]
#[ensures(f2.invariant())]
pub fn lemma_permut_formula_ok_invariant(f: Formula, f2: Formula, cref: Int) {}
*/

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(c.post_unit_inner(a))]
#[requires(c.invariant(a.len()))]
#[requires(c2.invariant(a.len()))]
#[requires(exists<i: Int>
    0 <= i && i < (@c).len() && @(@c)[i].idx === idx && (@c)[i].sat_inner(a))]
#[requires(c2.unsat_inner(a))]
#[ensures(c2.same_idx_same_polarity_except(c, idx))]
pub fn lemma_same_pol(c: Clause, c2: Clause, a: Seq<AssignedState>, idx: Int) {}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(c.post_unit_inner(a))]
#[requires(c.invariant(a.len()))]
#[requires(c2.invariant(a.len()))]
#[requires((@c)[c_idx].sat_inner(a))]
#[requires(c2.unsat_inner(a))]
#[requires(0 <= c_idx && c_idx < (@c).len())]
#[requires(0 <= c2_idx && c2_idx < (@c2).len())]
#[requires(c3.resolvent_of(c, c2, c2_idx, c_idx))]
#[ensures(c3.unsat_inner(a))]
pub fn lemma_resolved_post_and_unsat_is_unsat(
    c: Clause,
    c2: Clause,
    c3: Clause,
    a: Seq<AssignedState>,
    c_idx: Int,
    c2_idx: Int,
) {
}

// CDCL STUFF START
#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
//#[ensures(formula_invariant(f2))]
//#[ensures(f.1 === f2.1)]
#[requires(f2.0 === f.0.push(c))]
#[requires(formula_invariant(f))]
#[ensures((f.0).len() + 1 === (f2.0).len())]
#[ensures(forall<i: Int> 0 <= i && i < (f.0).len() ==> ((f.0)[i]).equals((f2.0)[i]))]
#[ensures(@(f2.0)[(f2.0).len()-1] === @c)]
pub fn lemma_eq_formulas(f: (Seq<Clause>, Int), f2: (Seq<Clause>, Int), c: Clause) {}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(equisat_extension_inner(c2, f))]
#[requires(c3.resolvent_of(c, c2, k, m))]
#[requires(eventually_sat_complete_no_ass(f))]
#[ensures(eventually_sat_complete_no_ass(((f.0).push(c3), f.1)))]
pub fn lemma_sat_gives_sat(
    f: (Seq<Clause>, Int),
    c: Clause,
    c2: Clause,
    c3: Clause,
    k: Int,
    m: Int,
) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(formula_invariant(f))]
#[requires(!eventually_sat_complete_no_ass(f))]
#[ensures(!eventually_sat_complete_no_ass(((f.0).push(c3), f.1)))]
pub fn lemma_not_sat_gives_not_sat(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(c2.in_formula_inner(f))]
#[requires(c3.resolvent_of(c, c2, k, m))]
//#[ensures(equisat_compatible_inner(f, (f.0.push(c3), f.1)))]
#[ensures(equisat_extension_inner(c3, f))]
pub fn lemma_extended_formula_is_equisat_compatible(
    f: (Seq<Clause>, Int),
    c: Clause,
    c2: Clause,
    c3: Clause,
    k: Int,
    m: Int,
) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    //lemma_not_sat_gives_not_sat(f, c, c2, c3, k, m);
    //lemma_sat_gives_sat(f, c, c2, c3, k, m);
}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(formula_invariant(f))]
#[requires(equisat_extension_inner(c, f))]
#[requires(c2.in_formula_inner(f))]
#[requires(c3.resolvent_of(c, c2, k, m))]
#[ensures(equisat_extension_inner(c3, f))]
pub fn lemma_resolvent_of_equisat_extension_is_equisat(
    f: (Seq<Clause>, Int),
    c: Clause,
    c2: Clause,
    c3: Clause,
    k: Int,
    m: Int,
) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    lemma_not_sat_gives_not_sat(f, c, c2, c3);
    lemma_sat_gives_sat(f, c, c2, c3, k, m);
    lemma_extended_formula_is_equisat_compatible(f, c, c2, c3, k, m);
}

// These are not currently in use
#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(formula_invariant(f))]
#[requires(equisat_extension_inner(c, f))]
#[ensures(equisat_compatible_inner(f, (f.0.push(c), f.1)))]
pub fn lemma_extending_with_equi_ext_is_equi_compat(f: (Seq<Clause>, Int), c: Clause) {}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(f.invariant())]
#[requires(f2.invariant())]
#[requires(f3.invariant())]
#[requires(f.equisat_compatible(f2))]
#[requires(f2.equisat_compatible(f3))]
#[ensures(f.equisat_compatible(f3))]
pub fn lemma_equisat_is_trans(f: Formula, f2: Formula, f3: Formula) {}
// CDCL STUFF END

#[cfg_attr(feature = "trust_logic_logic", trusted)]
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

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(f.invariant())]
#[requires(assignments_invariant(a, f))]
#[requires(complete_inner(a))]
#[ensures(f.unsat_inner(a) || f.sat_inner(a))]
pub fn lemma_complete_implies_sat_or_unsat(f: Formula, a: Seq<AssignedState>) {}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(f.invariant())]
#[requires(assignments_invariant(a, f))]
#[requires(complete_inner(a))]
#[requires(!f.sat_inner(a))]
#[ensures(f.unsat_inner(a))]
pub fn lemma_complete_and_not_sat_implies_unsat(f: Formula, a: Seq<AssignedState>) {
    lemma_complete_implies_sat_or_unsat(f, a);
}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(f.invariant())]
#[requires(assignments_invariant(a, f))]
#[requires(complete_inner(a))]
#[requires(!f.unsat_inner(a))]
#[ensures(f.sat_inner(a))]
pub fn lemma_complete_and_not_unsat_implies_sat(f: Formula, a: Seq<AssignedState>) {
    lemma_complete_implies_sat_or_unsat(f, a);
}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(f.invariant())]
#[requires(assignments_invariant(a, f))]
#[requires(f.unsat_inner(a))]
#[ensures(!f.eventually_sat_complete_inner(a))]
pub fn lemma_not_sat_formula_implies_unsat_formula(f: Formula, a: Seq<AssignedState>) {}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(c.unsat_inner(a))]
#[requires(c.in_formula(f))]
#[ensures(f.unsat_inner(a))]
pub fn lemma_not_sat_clause_implies_unsat_formula(f: Formula, c: Clause, a: Seq<AssignedState>) {}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
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

#[cfg_attr(feature = "trust_logic_logic", trusted)]
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
pub fn lemma_unit_wrong_polarity_unsat_formula(
    c: Clause,
    f: Formula,
    a: Seq<AssignedState>,
    ix: Int,
    v: AssignedState,
) {
    lemma_not_sat_formula_implies_unsat_formula(f, a);
    lemma_correct_polarity_makes_clause_sat(c, a, ix, v);
    lemma_incorrect_polarity_makes_clause_unsat(c, a, ix, v);
    lemma_not_sat_clause_implies_unsat_formula(f, c, a.set(ix, flip_v(v)));
}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(0 <= ix && ix < a.len())]
#[requires(exists<j: Int> 0 <= j && j < (@c).len() && @(@c)[j].idx === ix && bool_to_assignedstate((@c)[j].polarity) === v)]
#[ensures(c.sat_inner(a.set(ix, v)))]
pub fn lemma_correct_polarity_makes_clause_sat(
    c: Clause,
    a: Seq<AssignedState>,
    ix: Int,
    v: AssignedState,
) {
}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
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
pub fn lemma_incorrect_polarity_makes_clause_unsat(
    c: Clause,
    a: Seq<AssignedState>,
    ix: Int,
    v: AssignedState,
) {
}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(0 <= ix && ix < a.len() && unset(a[ix]))]
#[requires(f.eventually_sat_complete_inner(a.set(ix, v)))]
#[ensures(f.eventually_sat_complete_inner(a))]
pub fn lemma_extension_sat_base_sat(f: Formula, a: Seq<AssignedState>, ix: Int, v: AssignedState) {}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(0 <= ix && ix < a.len() && unset(a[ix]))]
#[requires(!f.eventually_sat_complete_inner(a.set(ix, neg())))]
#[requires(!f.eventually_sat_complete_inner(a.set(ix, pos())))]
#[ensures(!f.eventually_sat_complete_inner(a))]
pub fn lemma_extensions_unsat_base_unsat(a: Seq<AssignedState>, ix: Int, f: Formula) {
    compatible_inner(a, a.set(ix, pos()));
    compatible_inner(a, a.set(ix, neg()));
}
