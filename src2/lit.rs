extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::clause::*;
use assignments::Assignments;
use solver_dpll::bool_to_u8;

#[derive(Clone, Copy)]
pub struct Lit {
    pub idx: usize,
    pub polarity: bool,
}

// Predicates
impl Lit {
    #[predicate]
    pub fn invariant(self, n: Int) -> bool {
        pearlite! {
            @self.idx < n
        }
    }
    #[predicate]
    pub fn lit_in(self, c: Clause) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@c).len() &&
                (@c)[i] === self
        }
    }

    #[predicate]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! {
            self.sat_u8(@a)
        }
    }

    #[predicate]
    pub fn unset(self, a: Assignments) -> bool {
        pearlite! {
            @(@a)[@self.idx] >= 2
        }
    }

    #[predicate]
    pub fn unsat(self, a: Assignments) -> bool {
        pearlite! {
            self.unsat_u8(@a)
        }
    }

    #[predicate]
    pub fn sat_u8(self, a: Seq<u8>) -> bool {
        pearlite! {
            match self.polarity {
                true =>  (@a[@self.idx] == 1),
                false =>  (@a[@self.idx] == 0),
            }
        }
    }

    #[predicate]
    pub fn unsat_u8(self, a: Seq<u8>) -> bool {
        pearlite! {
            match self.polarity {
                true =>  (@a[@self.idx] == 0),
                false =>  (@a[@self.idx] == 1),
            }
        }
    }
    #[predicate]
    pub fn unset_u8(self, a: Seq<u8>) -> bool {
        pearlite! {
            @a[@self.idx] >= 2
        }
    }
}

impl Lit {
    #[inline]
    #[requires(self.invariant((@a).len()))]
    #[ensures(result === self.sat(*a))]
    pub fn lit_sat(self, a: &Assignments) -> bool {
        bool_to_u8(self.polarity) == a.0[self.idx]
    }
    #[inline]
    #[requires(self.invariant((@a).len()))]
    #[ensures(result === self.unsat(*a))]
    pub fn lit_unsat(self, a: &Assignments) -> bool {
        bool_to_u8(!self.polarity) == a.0[self.idx]
    }
    #[inline]
    #[requires(self.invariant((@a).len()))]
    #[ensures(result === self.unset(*a))]
    pub fn lit_unset(self, a: &Assignments) -> bool {
        a.0[self.idx] >= 2
    }
}
