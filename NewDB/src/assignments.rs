#![allow(non_snake_case)]
#![feature(type_ascription)]
#![cfg_attr(not(creusot), feature(stmt_expr_attributes, proc_macro_hygiene))]
extern crate creusot_contracts;

use creusot_contracts::{std::clone::Clone, std::*, vec, *};

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
pub struct Assignments(pub Vec<AssignedState>);

#[cfg(creusot)]
impl ShallowModel for Assignments {
    type ShallowModelTy = Seq<AssignedState>;

    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.0.shallow_model()
    }
}

impl Assignments {
    #[predicate]
    pub fn invariant(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self@.len() ==>
                self@[i]@ < 2
        }
    }
}

#[predicate]
pub fn complete_inner(a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < a.len() ==> !unset(a[i])
    }
}
