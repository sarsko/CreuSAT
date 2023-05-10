extern crate creusot_contracts;

use creusot_contracts::{std::clone::Clone, std::*, vec, *};

use crate::assignments::*;

use crate::logic_util::*;

/*
#[derive(Copy, Clone)]
pub struct Lit {
    pub code: u32,
}

#[cfg(creusot)]
impl ShallowModel for Lit {
    type ShallowModelTy = LitModel;

    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        LitModel { code: self.code.shallow_model() }
    }
}

impl Lit {
    #[ensures(result.code@ == code@)]
    pub(crate) fn raw(code: u32) -> Lit {
        Lit { code }
    }

    // TODO: Add support for shr
    #[inline(always)]
    #[ensures(result@ == self@.index_logic())]
    pub fn index(self) -> usize {
        //(self.code >> 1) as usize
        (self.code / 2) as usize
    }

    // TODO: Add support for &
    #[inline(always)]
    #[ensures(result == self@.is_positive_logic())]
    pub fn is_positive(self) -> bool {
        //self.code & 1 != 0
        self.code % 2 == 0
    }

    #[inline(always)]
    #[requires(self@.index_logic() < a@.0.len())]
    #[ensures(result == self@.sat(a@))]
    pub(crate) fn lit_sat(self, a: &Assignments) -> bool {
        a.0[self.index()] == self.is_positive() as u8
    }
}
*/

pub struct LitModel {
    pub code: Int,
}

impl LitModel {
    #[logic]
    #[why3::attr = "inline:trivial"]
    pub fn index_logic(self) -> Int {
        (self.code / 2) // Why do I need parans here ?
    }

    #[logic]
    #[why3::attr = "inline:trivial"]
    pub fn is_positive_logic(self) -> bool {
        self.code % 2 == 0
    }
}

impl LitModel {
    #[predicate]
    pub(crate) fn var_in_range(self, n: Int) -> bool {
        pearlite! {
            self.index_logic() < n
        }
    }

    // This is the one that is supposed to stay
    #[predicate]
    #[why3::attr = "inline:trivial"]
    pub(crate) fn sat(self, a: AssignmentsModel) -> bool {
        pearlite! {
            a.0[self.index_logic()] == bool_as_int(self.is_positive_logic())
        }
    }
}
