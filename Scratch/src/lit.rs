
use ::std::ops;
use creusot_contracts::{model::*, std::*, *};

use creusot_contracts::Clone;

use crate::{assignments::*, clause::*};

// ===== Lit =====
#[derive(Clone, Copy)]
pub struct Lit {
    pub idx: usize,
    pub polarity: bool,
}

#[cfg(creusot)]
impl View for Lit {
    type ViewTy = Lit;

    #[open]
    #[logic]
    fn view(self) -> Self {
        self
    }
}

#[cfg(creusot)]
impl DeepModel for Lit {
    type DeepModelTy = Lit;

    #[open]
    #[logic]
    fn deep_model(self) -> Self {
        self
    }
}

#[open]
#[predicate]
//#[ensures(result == self.lit_in_internalc@)]
#[why3::attr = "inline:trivial"]
pub fn idx_in_logic(idx: Int, c: Seq<Lit>) -> bool {
    pearlite! {
        exists<i: Int> 0 <= i && i < c.len() &&
            c[i].index_logic() == idx
    }
}

// Logic
impl Lit {
    #[open]
    #[logic]
    #[why3::attr = "inline:trivial"]
    pub fn index_logic(self) -> Int {
        pearlite! { self.idx@ }
    }

    #[open]
    #[logic]
    #[why3::attr = "inline:trivial"]
    pub fn is_positive_logic(self) -> bool {
        pearlite! { self.polarity }
    }

    #[open]
    #[logic]
    #[why3::attr = "inline:trivial"]
    pub fn to_watchidx_logic(self) -> Int {
        pearlite! { self.index_logic() * 2 + if self.is_positive_logic() { 0 } else { 1 } }
    }

    #[open]
    #[logic]
    #[why3::attr = "inline:trivial"]
    pub fn to_neg_watchidx_logic(self) -> Int {
        pearlite! { self.index_logic() * 2 + if self.is_positive_logic() { 1 } else { 0 } }
    }
}

// Predicates
impl Lit {
    #[open]
    #[predicate]
    pub fn is_opp(self, o: Lit) -> bool {
        pearlite! {
            self.index_logic() == o.index_logic() && self.is_positive_logic() != o.is_positive_logic()
        }
    }

    #[open]
    #[predicate]
    pub fn lit_in_internal(self, c: Seq<Lit>) -> bool {
        pearlite! { exists<i: Int> 0 <= i && i < c.len() && c[i] == self }
    }

    #[open]
    #[predicate]
    pub fn lit_in(self, c: Clause) -> bool {
        pearlite! { exists<i: Int> 0 <= i && i < c@.len() && c@[i] == self }
    }

    #[open]
    #[predicate]
    pub fn lit_idx_in(self, c: Clause) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < c@.len() &&
                c@[i].index_logic() == self.index_logic()
        }
    }

    #[open]
    #[predicate]
    pub fn inv(self, n: Int) -> bool {
        pearlite! { self.index_logic() < n }
    }

    #[open]
    #[predicate]
    pub fn sat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            match self.is_positive_logic() {
                true  =>  (a[self.index_logic()]@ == 1),
                false =>  (a[self.index_logic()]@ == 0),
            }
        }
    }

    #[open]
    #[predicate]
    pub fn unsat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            match self.is_positive_logic() {
                true  =>  (a[self.index_logic()]@ == 0),
                false =>  (a[self.index_logic()]@ == 1),
            }
        }
    }

    #[open]
    #[predicate]
    pub fn unset_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! { a[self.index_logic()]@ >= 2 }
    }

    #[open]
    #[predicate]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! { self.sat_inner(a@) }
    }

    #[open]
    #[predicate]
    pub fn unset(self, a: Assignments) -> bool {
        pearlite! { self.unset_inner(a@) }
    }

    #[open]
    #[predicate]
    pub fn unsat(self, a: Assignments) -> bool {
        pearlite! { self.unsat_inner(a@) }
    }

    /*
        #[open]
    #[predicate]
        pub fn idx_in_trail(self, t: Vec<Step>) -> bool {
            pearlite! {
                exists<i: Int> 0 <= i && i < (@t).len() &&
                    (@t)[i].lit.index_logic() == self.index_logic()
            }
        }
        */
}
