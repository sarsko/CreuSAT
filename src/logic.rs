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
#[requires(u >= i)]
#[requires(i >= 0)]
#[variant(u-i)]
#[ensures(result > 0 === (exists<j: Int> i <= j && j < u && a[@c[j].idx] === AssignedState::Unset))]
#[ensures((forall<j: Int> i <= j && j < u ==> !(a[@c[j].idx] === AssignedState::Unset)) ==> result === 0)]
pub fn unassigned_count_clause_internal(c: Seq<Lit>, a: Seq<AssignedState>, i: Int, u: Int) -> Int {
    if i == u {
        0
    } else if pearlite! { a[@c[i].idx] === AssignedState::Unset } {
        1 + unassigned_count_clause_internal(c, a, i + 1, u)
    } else {
        unassigned_count_clause_internal(c, a, i + 1, u)
    }
}

#[logic]
#[ensures(result > 0 ==> exists<i: Int> 0 <= i && i < c.len() && a[@c[i].idx] === AssignedState::Unset)]
pub fn unassigned_count_clause(c: Seq<Lit>, a: Seq<AssignedState>) -> Int {
    unassigned_count_clause_internal(c, a, 0, c.len())
}

#[logic]
#[variant(c.len())]
#[ensures(result > 0 ==> exists<i: Int> 0 <= i && i < c.len() && a[@c[i].idx] === AssignedState::Unset)]
#[ensures(result === unassigned_count_clause_partial(c, a, c.len()))]
pub fn unassigned_count_clause_old(c: Seq<Lit>, a: Seq<AssignedState>) -> Int {
    if c.len() == 0 {
        0
    } else if pearlite! { a[@c[0].idx] === AssignedState::Unset } {
        1 + unassigned_count_clause_old(c.tail(), a)
    } else {
        unassigned_count_clause_old(c.tail(), a)
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