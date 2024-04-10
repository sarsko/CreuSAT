extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{assignments::*, clause::*, lit::*, trail::*};

#[predicate]
#[open]
//#[ensures(result == self.lit_in_internal(c))]
#[why3::attr = "inline:trivial"]
pub fn idx_in_logic(idx: Int, c: Seq<Lit>) -> bool {
    pearlite! {
        exists<i: Int> 0 <= i && i < c.len() &&
            c[i].index_logic() == idx
    }
}

// Logic
impl Lit {
    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    pub fn index_logic(self) -> Int {
        pearlite! { self.idx@ }
    }

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    pub fn is_positive_logic(self) -> bool {
        pearlite! { self.polarity }
    }

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    pub fn to_watchidx_logic(self) -> Int {
        pearlite! { self.index_logic() * 2 + if self.is_positive_logic() { 0 } else { 1 } }
    }

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    pub fn to_neg_watchidx_logic(self) -> Int {
        pearlite! { self.index_logic() * 2 + if self.is_positive_logic() { 1 } else { 0 } }
    }
}

// Predicates
impl Lit {
    #[predicate]
    #[open]
    pub fn is_opp(self, o: Lit) -> bool {
        pearlite! {
            self.index_logic() == o.index_logic() && self.is_positive_logic() != o.is_positive_logic()
        }
    }

    #[predicate]
    #[open]
    pub fn lit_in_internal(self, c: Seq<Lit>) -> bool {
        pearlite! { exists<i: Int> 0 <= i && i < c.len() && c[i] == self }
    }

    #[predicate]
    #[open]
    pub fn lit_in(self, c: Clause) -> bool {
        pearlite! { exists<i: Int> 0 <= i && i < c@.len() && c@[i] == self }
    }

    #[predicate]
    #[open]
    pub fn lit_idx_in(self, c: Clause) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < c@.len() &&
                c@[i].index_logic() == self.index_logic()
        }
    }

    #[predicate]
    #[open]
    pub fn invariant(self, n: Int) -> bool {
        pearlite! { self.index_logic() < n }
    }

    #[predicate]
    #[open]
    pub fn sat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            match self.is_positive_logic() {
                true  =>  (a[self.index_logic()]@ == 1),
                false =>  (a[self.index_logic()]@ == 0),
            }
        }
    }

    #[predicate]
    #[open]
    pub fn unsat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            match self.is_positive_logic() {
                true  =>  (a[self.index_logic()]@ == 0),
                false =>  (a[self.index_logic()]@ == 1),
            }
        }
    }

    #[predicate]
    #[open]
    pub fn unset_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! { a[self.index_logic()]@ >= 2 }
    }

    #[predicate]
    #[open]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! { self.sat_inner(a@) }
    }

    #[predicate]
    #[open]
    pub fn unset(self, a: Assignments) -> bool {
        pearlite! { self.unset_inner(a@) }
    }

    #[predicate]
    #[open]
    pub fn unsat(self, a: Assignments) -> bool {
        pearlite! { self.unsat_inner(a@) }
    }

    #[predicate]
    #[open]
    pub fn idx_in_trail(self, t: Vec<Step>) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < t@.len() &&
                t@[i].lit.index_logic() == self.index_logic()
        }
    }
}
