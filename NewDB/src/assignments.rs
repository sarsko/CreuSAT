#![allow(non_snake_case)]
#![feature(type_ascription)]
#![cfg_attr(not(creusot), feature(stmt_expr_attributes, proc_macro_hygiene))]
extern crate creusot_contracts;

use creusot_contracts::{std::clone::Clone, std::*, vec, *};

pub type AssignedState = u8;

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
            forall<i: Int> 0 <= i && i < (@self).len() ==>
                @(@self)[i] < 2
        }
    }
}
