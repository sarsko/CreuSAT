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
//#[ensures(formula_invariant(f2))]
//#[ensures(f.1 === f2.1)]
#[requires(f2.0 === f.0.push(c))]
#[requires(formula_invariant(f))]
#[ensures((f.0).len() + 1 === (f2.0).len())]
#[ensures(forall<i: Int> 0 <= i && i < (f.0).len() ==> ((f.0)[i]).equals((f2.0)[i]))]
#[ensures(@(f2.0)[(f2.0).len()-1] === @c)]
pub fn lemma_eq_formulas(f: (Seq<Clause>, Int), f2: (Seq<Clause>, Int), c: Clause) {}

#[trusted] // OK
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(equisat_extension_inner(c2, f))]
#[requires(c3.resolvent_of(c, c2, k, m))]
#[requires(eventually_sat_complete_no_ass(f))]
#[ensures(eventually_sat_complete_no_ass(((f.0).push(c3), f.1)))]
pub fn lemma_sat_gives_sat(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, k: Int, m: Int) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
}

#[trusted] // OK
#[logic]
#[requires(formula_invariant(f))]
#[requires(!eventually_sat_complete_no_ass(f))]
#[ensures(!eventually_sat_complete_no_ass(((f.0).push(c3), f.1)))]
pub fn lemma_not_sat_gives_not_sat(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
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
    //lemma_not_sat_gives_not_sat(f, c, c2, c3, k, m);
    //lemma_sat_gives_sat(f, c, c2, c3, k, m);
}

#[trusted] // OK
#[logic]
#[requires(formula_invariant(f))]
#[requires(equisat_extension_inner(c, f))]
#[requires(c2.in_formula_inner(f))]
#[requires(c3.resolvent_of(c, c2, k, m))]
#[ensures(equisat_extension_inner(c3, f))]
pub fn lemma_resolvent_of_equisat_extension_is_equisat(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, k: Int, m: Int) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    lemma_not_sat_gives_not_sat(f, c, c2, c3);
    lemma_sat_gives_sat(f, c, c2, c3, k, m);
    lemma_extended_formula_is_equisat_compatible(f, c, c2, c3, k, m);
}


// These are not currently in use
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
