#![allow(non_snake_case)]
#![feature(type_ascription)]
#![cfg_attr(not(creusot), feature(stmt_expr_attributes, proc_macro_hygiene))]
extern crate creusot_contracts;

use creusot_contracts::{std::clone::Clone, std::*, vec, *};

/*
pub type AssignedState = u8;

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
    pearlite! { v@ >= 2 }
}

#[derive(Clone)]
pub(crate) struct Assignments(pub Vec<AssignedState>);

#[cfg(creusot)]
impl ShallowModel for Assignments {
    type ShallowModelTy = AssignmentsModel;

    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        AssignmentsModel(self.0.shallow_model())
    }
}
*/

#[predicate]
pub fn unset(v: Int) -> bool {
    pearlite! { v >= 2 }
}

pub struct AssignmentsModel(pub Seq<Int>);

impl AssignmentsModel {
    #[predicate]
    pub fn invariant(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self.0.len() ==>
                0 <= self.0[i] //&& self.0[i] < 2 // Why did I have this? It is just wrong ?
        }
    }

    #[predicate]
    pub fn complete(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self.0.len() ==> !unset(self.0[i])
        }
    }
}
