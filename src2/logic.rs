extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;
use crate::lit::*;
use crate::clause::*;
use crate::assignments::*;
use crate::formula::*;

#[logic]
#[ensures(b ==> result === AssignedState::Positive)]
#[ensures(!b ==> result === AssignedState::Negative)]
pub fn bool_to_assignedstate(b: bool) -> AssignedState {
    if b {
        AssignedState::Positive
    } else {
        AssignedState::Negative
    }
}

#[logic]
fn flip_v(v: AssignedState) -> AssignedState {
    match v {
        AssignedState::Unset => AssignedState::Unset,
        AssignedState::Positive => AssignedState::Negative,
        AssignedState::Negative => AssignedState::Positive,
    }
}

#[logic] 
#[requires(f.invariant())]
#[requires(assignments_invariant(a, f))]
#[requires(f.unsat_inner(a))]
#[ensures(!f.eventually_sat_complete_inner(a))]
pub fn lemma_not_sat_formula_implies_unsat_formula(f: Formula, a: Seq<AssignedState>) {}

#[logic]
#[requires(c.unsat_inner(a))]
#[requires(c.in_formula(f))]
#[ensures(f.unsat_inner(a))]
pub fn lemma_not_sat_clause_implies_unsat_formula(f: Formula, c: Clause, a: Seq<AssignedState>) {}


#[logic]
#[requires(f.invariant())]
#[requires(@f.num_vars === a.len())]
#[requires(0 <= ix && ix < a.len() && a[ix] === AssignedState::Unset)]
#[requires(v === AssignedState::Positive || v === AssignedState::Negative)]
#[requires(f.eventually_sat_complete_inner(a))]
#[requires(!f.eventually_sat_complete_inner(a.set(ix, flip_v(v))))]
#[ensures(f.eventually_sat_complete_inner(a.set(ix, v)))]
pub fn lemma_unit_forces(c: Clause, f: Formula, a: Seq<AssignedState>, ix: Int, v: AssignedState) {
    lemma_not_sat_formula_implies_unsat_formula(f, a);
}

#[logic]
#[requires(f.invariant())]
#[requires(@f.num_vars === a.len())]
#[requires(0 <= ix && ix < a.len() && a[ix] === AssignedState::Unset)]
#[requires(v === AssignedState::Positive || v === AssignedState::Negative)]
#[requires(c.unit_inner(a))]
#[requires(c.in_formula(f))]
#[requires(forall<j: Int> 0 <= j && j < (@c).len() ==> 0 <= @(@c)[j].idx && @(@c)[j].idx < a.len())]
#[requires(exists<j: Int> 0 <= j && j < (@c).len() && @(@c)[j].idx === ix && bool_to_assignedstate(((@c)[j].polarity)) === v)]
#[requires(forall<j: Int> 0 <= j && j < (@c).len() && !(@(@c)[j].idx === ix) ==> !(a[@(@c)[j].idx] === AssignedState::Unset))]
#[requires(forall<j: Int, k: Int> 0 <= j && j < (@c).len() && k < j ==> !(@(@c)[k].idx === @(@c)[j].idx))]
#[requires(forall<j: Int> 0 <= j && j < (@c).len() && !(@(@c)[j].idx === ix) ==> !(a[@(@c)[j].idx] === bool_to_assignedstate((@c)[j].polarity)))]
#[ensures(!f.eventually_sat_complete_inner(a.set(ix, flip_v(v))))]
#[ensures(f.unsat_inner(a.set(ix, flip_v(v))))]
pub fn lemma_unitClauseLiteralFalse_tauNotSatisfiable(c: Clause, f: Formula, a: Seq<AssignedState>, ix: Int, v: AssignedState) {
    lemma_not_sat_formula_implies_unsat_formula(f, a);
    lemma_correctPolarityMakesClauseSat(c, a, ix, v);
    lemma_incorrectPolarityMakesClauseUnsat(c, a, ix, v);
    lemma_not_sat_clause_implies_unsat_formula(f, c, a.set(ix, flip_v(v)));
}

#[logic]
#[requires(0 <= ix && ix < a.len())]
#[requires(exists<j: Int> 0 <= j && j < (@c).len() && @(@c)[j].idx === ix && bool_to_assignedstate((@c)[j].polarity) === v)]
#[ensures(c.sat_inner(a.set(ix, v)))]
pub fn lemma_correctPolarityMakesClauseSat(c: Clause, a: Seq<AssignedState>, ix: Int, v: AssignedState) {}

#[logic]
#[requires(0 <= ix && ix < a.len() && a[ix] === AssignedState::Unset)]
#[requires(c.unit_inner(a))]
#[requires(!c.sat_inner(a))]
#[requires(v === AssignedState::Positive || v === AssignedState::Negative)] 
#[requires(exists<j: Int> 0 <= j && j < (@c).len() && @(@c)[j].idx === ix && bool_to_assignedstate((@c)[j].polarity) === v)]
#[requires(forall<j: Int> 0 <= j && j < (@c).len() ==> 0 <= @(@c)[j].idx && @(@c)[j].idx < a.len())]
#[requires(forall<j: Int, k: Int> 0 <= j && j < (@c).len() && k < j ==> !(@(@c)[k].idx === @(@c)[j].idx))]
#[requires(forall<j: Int> 0 <= j && j < (@c).len() && !(@(@c)[j].idx === ix) ==> !(a[@(@c)[j].idx] === AssignedState::Unset))]
#[requires(forall<j: Int> 0 <= j && j < (@c).len() && !(@(@c)[j].idx === ix) ==> !(a[@(@c)[j].idx] === bool_to_assignedstate((@c)[j].polarity)))]
#[ensures(forall<j: Int> 0 <= j && j < (@c).len()  ==> !((a.set(ix, v))[@(@c)[j].idx] === AssignedState::Unset))]
#[ensures(!(a.set(ix, flip_v(v))[ix] === AssignedState::Unset))]
#[ensures(c.unsat_inner(a.set(ix, flip_v(v))))]
#[ensures(!c.sat_inner(a.set(ix, flip_v(v))))]
pub fn lemma_incorrectPolarityMakesClauseUnsat(c: Clause, a: Seq<AssignedState>, ix: Int, v: AssignedState) {}

#[logic]
#[requires(0 <= ix && ix < a.len() && a[ix] === AssignedState::Unset)]
#[requires(f.eventually_sat_complete_inner(a.set(ix, v)))]
#[ensures(f.eventually_sat_complete_inner(a))]
pub fn lemma_extensionSat_baseSat(f: Formula, a: Seq<AssignedState>, ix: Int, v: AssignedState) {}

#[logic]
#[requires(0 <= ix && ix < a.len() && a[ix] === AssignedState::Unset)]
#[requires(!f.eventually_sat_complete_inner(a.set(ix, AssignedState::Positive)))]
#[requires(!f.eventually_sat_complete_inner(a.set(ix, AssignedState::Negative)))]
#[ensures(!f.eventually_sat_complete_inner(a))]
pub fn lemma_extensionsUnsat_baseUnsat(a: Seq<AssignedState>, ix: Int, f: Formula) {
    compatible_inner(a, a.set(ix, AssignedState::Positive));
    compatible_inner(a, a.set(ix, AssignedState::Negative));
}
