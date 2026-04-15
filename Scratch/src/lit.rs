use ::std::ops;
use creusot_std::prelude::{Clone, *};

use crate::{assignments::*, clause::*};

// ===== Lit =====
#[derive(Clone, Copy)]
pub struct Lit {
    pub idx: usize,
    pub polarity: bool,
}

impl View for Lit {
    type ViewTy = Lit;

    #[logic]
    fn view(self) -> Self {
        self
    }
}

impl DeepModel for Lit {
    type DeepModelTy = Lit;

    #[logic]
    fn deep_model(self) -> Self {
        self
    }
}

#[logic(inline)]
//#[ensures(result == self.lit_in_internalc@)]
pub fn idx_in_logic(idx: Int, c: Seq<Lit>) -> bool {
    pearlite! {
        exists<i: Int> 0 <= i && i < c.len() &&
            c[i].index_logic() == idx
    }
}

// Logic
impl Lit {
    #[logic(inline)]
    pub fn index_logic(self) -> Int {
        pearlite! { self.idx@ }
    }

    #[logic(inline)]
    pub fn is_positive_logic(self) -> bool {
        pearlite! { self.polarity }
    }

    #[logic(inline)]
    pub fn to_watchidx_logic(self) -> Int {
        pearlite! { self.index_logic() * 2 + if self.is_positive_logic() { 0 } else { 1 } }
    }

    #[logic(inline)]
    pub fn to_neg_watchidx_logic(self) -> Int {
        pearlite! { self.index_logic() * 2 + if self.is_positive_logic() { 1 } else { 0 } }
    }
}

// Predicates
impl Lit {
    #[logic]
    pub fn is_opp(self, o: Lit) -> bool {
        pearlite! {
            self.index_logic() == o.index_logic() && self.is_positive_logic() != o.is_positive_logic()
        }
    }

    #[logic]
    pub fn lit_in_internal(self, c: Seq<Lit>) -> bool {
        pearlite! { exists<i: Int> 0 <= i && i < c.len() && c[i] == self }
    }

    #[logic]
    pub fn lit_in(self, c: Clause) -> bool {
        pearlite! { exists<i: Int> 0 <= i && i < c@.len() && c@[i] == self }
    }

    #[logic]
    pub fn lit_idx_in(self, c: Clause) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < c@.len() &&
                c@[i].index_logic() == self.index_logic()
        }
    }

    #[logic]
    pub fn inv(self, n: Int) -> bool {
        pearlite! { self.index_logic() < n }
    }

    #[logic]
    pub fn sat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            match self.is_positive_logic() {
                true  =>  (a[self.index_logic()]@ == 1),
                false =>  (a[self.index_logic()]@ == 0),
            }
        }
    }

    #[logic]
    pub fn unsat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            match self.is_positive_logic() {
                true  =>  (a[self.index_logic()]@ == 0),
                false =>  (a[self.index_logic()]@ == 1),
            }
        }
    }

    #[logic]
    pub fn unset_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! { a[self.index_logic()]@ >= 2 }
    }

    #[logic]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! { self.sat_inner(a@) }
    }

    #[logic]
    pub fn unset(self, a: Assignments) -> bool {
        pearlite! { self.unset_inner(a@) }
    }

    #[logic]
    pub fn unsat(self, a: Assignments) -> bool {
        pearlite! { self.unsat_inner(a@) }
    }

    /*
    #[logic(open)]
    pub fn idx_in_trail(self, t: Vec<Step>) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@t).len() &&
                (@t)[i].lit.index_logic() == self.index_logic()
        }
    }
    */
}
