extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;
use crate::ghost;
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
