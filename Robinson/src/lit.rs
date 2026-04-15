use creusot_std::prelude::{Clone, *};

use crate::assignments::*;

#[cfg(creusot)]
use crate::clause::*;

#[derive(Clone, Copy)]
pub struct Lit {
    pub idx: usize,
    pub polarity: bool,
}

// Logic
impl Lit {
    #[logic(open, inline)]
    pub fn index_logic(self) -> Int {
        pearlite! { self.idx@ }
    }
}

// Predicates
impl Lit {
    #[logic(open)]
    pub fn lit_in(self, c: Clause) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < c@.len() && c@[i] == self
        }
    }

    #[logic(open)]
    pub fn inv(self, n: Int) -> bool {
        pearlite! { self.idx@ < n }
    }

    #[logic(open)]
    pub fn sat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            match self.polarity {
                true  =>  (a[self.idx@]@ == 1),
                false =>  (a[self.idx@]@ == 0),
            }
        }
    }

    #[logic(open)]
    pub fn unsat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            match self.polarity {
                true  =>  (a[self.idx@]@ == 0),
                false =>  (a[self.idx@]@ == 1),
            }
        }
    }

    #[logic(open)]
    pub fn unset_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            a[self.idx@]@ >= 2
        }
    }

    #[logic(open)]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! {
            self.sat_inner(a@)
        }
    }

    #[logic(open)]
    pub fn unset(self, a: Assignments) -> bool {
        pearlite! { self.unset_inner(a@) }
    }

    #[logic(open)]
    pub fn unsat(self, a: Assignments) -> bool {
        pearlite! { self.unsat_inner(a@) }
    }
}

impl Lit {
    #[inline(always)]
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[ensures(result@ == self.index_logic())]
    pub fn index(self) -> usize {
        self.idx
    }

    #[inline]
    #[requires(self.inv(a@.len()))]
    #[ensures(result == self.sat(*a))]
    pub fn lit_sat(self, a: &Assignments) -> bool {
        match self.polarity {
            true => (a.0[self.idx] == 1),
            false => (a.0[self.idx] == 0),
        }
    }

    #[allow(unused)] // Not used, but OK to have.
    #[inline]
    #[requires(self.inv(a@.len()))]
    #[ensures(result == self.unsat(*a))]
    pub fn lit_unsat(self, a: &Assignments) -> bool {
        match self.polarity {
            true => (a.0[self.idx] == 0),
            false => (a.0[self.idx] == 1),
        }
    }

    #[inline]
    #[requires(self.inv(a@.len()))]
    #[ensures(result == self.unset(*a))]
    pub fn lit_unset(self, a: &Assignments) -> bool {
        a.0[self.idx] >= 2
    }

    #[inline(always)]
    //#[cfg_attr(feature = "trust_lit", trusted)]
    #[ensures(result == self.inv(n@))]
    #[ensures(result == (self.idx@ < n@))]
    pub fn check_lit_invariant(&self, n: usize) -> bool {
        self.idx < n
    }
}
