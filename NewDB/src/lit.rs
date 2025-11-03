use creusot_contracts::prelude::{Clone, *};

use crate::assignments::*;

use crate::logic_util::*;

#[derive(Copy, Clone)]
pub struct Lit {
    pub code: u32,
}

impl Lit {
    #[logic(open, inline)]
    pub fn index_logic(self) -> Int {
        pearlite! { self.code@ / 2 }
    }

    #[logic(open, inline)]
    pub fn is_positive_logic(self) -> bool {
        pearlite! { self.code@ % 2 == 0 }
    }
}

impl Lit {
    #[logic(open)]
    pub fn var_in_range(self, n: Int) -> bool {
        pearlite! {
            self.index_logic() < n
        }
    }

    #[logic(open, inline)]
    pub fn lit_sat_logic(self, a: Assignments) -> bool {
        pearlite! {
            a@[self.index_logic()] == bool_as_u8(self.is_positive_logic())
        }
    }

    // This is the one that is supposed to stay
    #[logic(open, inline)]
    pub fn sat(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            a[self.index_logic()] == bool_as_u8(self.is_positive_logic())
        }
    }
}

impl Lit {
    #[check(ghost)]
    #[ensures(result.code@ == code@)]
    pub(crate) fn raw(code: u32) -> Lit {
        Lit { code }
    }

    // TODO: Add support for shr
    #[inline(always)]
    #[check(ghost)]
    #[ensures(result@ == self.index_logic())]
    pub fn index(self) -> usize {
        //(self.code >> 1) as usize
        (self.code / 2) as usize
    }

    // TODO: Add support for &
    #[inline(always)]
    #[check(ghost)]
    #[ensures(result == self.is_positive_logic())]
    pub fn is_positive(self) -> bool {
        //self.code & 1 != 0
        self.code % 2 == 0
    }

    #[inline(always)]
    #[check(ghost)]
    #[requires(self.index_logic() < a@.len())]
    #[ensures(result == self.lit_sat_logic(*a))]
    pub fn lit_sat(self, a: &Assignments) -> bool {
        a.0[self.index()] == self.is_positive() as u8
    }
}
