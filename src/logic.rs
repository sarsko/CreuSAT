extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;
use crate::ghost;
use crate::lit::*;
use crate::clause::*;
use crate::predicates::*;
use crate::assignments::*;
use crate::formula::*;

#[logic]
#[ensures((result === 1) === a[@c[i].idx] === AssignedState::Unset)]
#[ensures((result === 0) === !(a[@c[i].idx] === AssignedState::Unset))]
#[requires(i < c.len())]
pub fn unassigned_count_once(c: Seq<Lit>, a: Seq<AssignedState>, i: Int) -> Int {
    if pearlite! { a[@c[i].idx] === AssignedState::Unset } {
        1
    } else {
        0
    }
}

#[logic]
#[requires(u >= i)]
#[requires(i >= 0)]
#[variant(u-i)]
#[ensures(result > 0 === (exists<j: Int> i <= j && j < u && a[@c[j].idx] === AssignedState::Unset))]
#[ensures((forall<j: Int> i <= j && j < u ==> !(a[@c[j].idx] === AssignedState::Unset)) ==> result === 0)]
/*
#[ensures(result > 0 ==> ((a[@c[i].idx] === AssignedState::Unset && 
unassigned_count_clause_internal(c, a, i-1, u-1) === result - 1) ||
unassigned_count_clause_internal(c, a, i-1, u-1) === result))]
*/
pub fn unassigned_count_clause_internal(c: Seq<Lit>, a: Seq<AssignedState>, i: Int, u: Int) -> Int {
    if i == u {
        0
    } else {
        unassigned_count_once(c, a, i) + unassigned_count_clause_internal(c, a, i + 1, u)
    }
}

#[logic]
#[requires(i <= c.len())]
#[variant(c.len())]
pub fn unassigned_count_clause_partial(c: Seq<Lit>, a: Seq<AssignedState>, i: Int) -> Int {
    unassigned_count_clause_internal(c, a, 0, i)
}

#[logic]
#[ensures(result > 0 ==> exists<i: Int> 0 <= i && i < c.len() && a[@c[i].idx] === AssignedState::Unset)]
pub fn unassigned_count_clause(c: Seq<Lit>, a: Seq<AssignedState>) -> Int {
    unassigned_count_clause_internal(c, a, 0, c.len())
}

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
#[requires(unit_internal(c, a))]
#[requires(0 <= i && i < c.len())]
#[ensures(is_unass_in(c, result, a))]
#[ensures(contains(c, result))]
#[variant(c.len() - i)]
pub fn unit_get_literal_internal(c: Seq<Lit>, a: Seq<AssignedState>, i: Int) -> Lit {
    if pearlite! { a[@c[i].idx] === AssignedState::Unset} {
        c[i]
    } else {
        unit_get_literal_internal(c, a, i + 1)
    }
}

#[logic]
#[requires(c.unit(a))]
pub fn unit_get_literal(c: Clause, a: Assignments) -> Lit {
    pearlite! { unit_get_literal_internal(@c, @a, 0) }
}

#[logic]
#[requires(c.unsat(a))]
#[ensures(unassigned_count_clause(@c, @a) === 0)]
#[ensures(!c.unit(a))]
fn lemma_unsat_implies_not_unit(c: Clause, a: Assignments) {}


#[logic]
#[requires(unit_internal(c, a))]
#[ensures(exists<i: Int> 0 <= i && i < c.len() ==> a[@c[i].idx] === AssignedState::Unset)]
fn lemma_unit_implies_unset(c: Seq<Lit>, a: Seq<AssignedState>) {}

#[logic]
#[requires(0 <= ix && ix < a.len())]
#[requires(a[ix] === AssignedState::Unset)]
#[requires(eventually_unsat_formula_inner(a.set(ix, AssignedState::Positive), f))]
#[requires(eventually_unsat_formula_inner(a.set(ix, AssignedState::Negative), f))]
#[ensures(eventually_unsat_formula_inner(a, f))]
fn lemma_eventually_assigned(a: Seq<AssignedState>, ix: Int, f: Formula) {
    compatible_inner(a, a.set(ix, AssignedState::Positive));
    compatible_inner(a, a.set(ix, AssignedState::Negative));
}

#[logic]
#[requires(0 <= @l.idx && @l.idx < a.len())]
#[requires(a[@l.idx] === AssignedState::Unset)]
#[ensures(eventually_sat_formula_inner(a, f))]
#[requires(eventually_sat_formula_inner(a.set(@l.idx, AssignedState::Positive), f) ||
eventually_sat_formula_inner(a.set(@l.idx, AssignedState::Negative), f))]
fn lemma_has_to_assign(c: Seq<Lit>, l: Lit, a: Seq<AssignedState>, f: Formula) {
    pearlite! {
    compatible_inner(a, a.set(@l.idx, AssignedState::Positive)) &&
    compatible_inner(a, a.set(@l.idx, AssignedState::Negative)) 
    };
}

#[logic]
#[requires(0 <= @l.idx && @l.idx < a.len())]
#[requires(a[@l.idx] === AssignedState::Unset)]
#[requires(l.polarity)]
#[requires(unit_internal(c, a))]
#[requires(eventually_sat_formula_inner(a, f))]
#[ensures(eventually_unsat_formula_inner(a.set(@l.idx, AssignedState::Negative), f))]
fn lemma_t(c: Seq<Lit>, l: Lit, a: Seq<AssignedState>, f: Formula) {}

