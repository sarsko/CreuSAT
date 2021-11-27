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
#[variant(a.len())]
pub fn unassigned_count(a: Seq<AssignedState>) -> Int {
    if a.len() == 0 {
        0
    } else if pearlite! { a[0] === AssignedState::Unset } {
        1 + unassigned_count(a.tail())
    } else {
        unassigned_count(a.tail())
    }
}

#[logic]
#[variant(c.len())]
pub fn unassigned_count_clause_partial(c: Seq<Lit>, a: Seq<AssignedState>, i: Int) -> Int {
    if c.len() == 0  || i == 0 {
        0
    } else if pearlite! { a[@c[0].idx] === AssignedState::Unset } {
            1 + unassigned_count_clause_partial(c.tail(), a, i - 1)
    } else {
            unassigned_count_clause_partial(c.tail(), a, i - 1)
    }
}

#[logic]
#[variant(c.len())]
pub fn unassigned_count_clause(c: Seq<Lit>, a: Seq<AssignedState>) -> Int {
    if c.len() == 0 {
        0
    } else if pearlite! { a[@c[0].idx] === AssignedState::Unset } {
            1 + unassigned_count_clause(c.tail(), a)
    } else {
            unassigned_count_clause(c.tail(), a)
    }
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
#[trusted]
#[requires(c.unit(a))]
#[requires(0 <= i && i < (@c).len())]
#[variant((@c).len() - i)]
pub fn unit_get_literal_internal(c: Clause, a: Assignments, i: Int) -> Lit {
    pearlite! {
        if (@a.0)[@(@c.0)[i].idx] === AssignedState::Unset {
            (@c.0)[i]
        } else {
            unit_get_literal_internal(c, a, i + 1)
        }
    }
}

#[logic]
#[requires(c.unit(a))]
pub fn unit_get_literal(c: Clause, a: Assignments) -> Lit {
    unit_get_literal_internal(c, a, 0)
}

#[logic]
pub fn has_to_assign(c: Clause, a: Assignments) -> bool{
    pearlite! {
        c.unit(a) ==> sat_clause_inner((@a).set(@unit_get_literal(c, a).idx, bool_to_assignedstate(unit_get_literal(c, a).polarity)), c)
    }
}

#[logic]
#[ensures(result === !b)]
pub fn flipbool(b: bool) -> bool {
    !b
}