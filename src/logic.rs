extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;
use crate::ghost;
use crate::lit::*;
use crate::clause::*;
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
