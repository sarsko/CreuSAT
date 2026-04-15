use creusot_std::prelude::*;

use crate::assignments::*;

#[logic(open)]
fn pos() -> AssignedState {
    1u8
}

#[logic(open)]
fn neg() -> AssignedState {
    0u8
}

#[logic(open)]
pub fn unset(v: AssignedState) -> bool {
    pearlite! {
        if v@ >= 2 {
            true
        } else {
            false
        }
    }
}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic(open)]
#[ensures(b ==> result@ == 1)]
#[ensures(!b ==> result@ == 0)]
pub fn bool_to_assignedstate(b: bool) -> AssignedState {
    if b {
        1u8
    } else {
        0u8
    }
}

#[logic(open)]
fn flip_v(v: AssignedState) -> AssignedState {
    pearlite! {
        if v@ == 0 {
            1u8
        } else if v@ == 1 {
            0u8
        } else {
            v
        }
    }
}
