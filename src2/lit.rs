extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::clause::*;
use crate::assignments::*;

#[derive(Clone, Copy)]
pub struct Lit {
    pub idx: usize,
    pub polarity: bool,
}

// Predicates
impl Lit {
    #[predicate]
    pub fn lit_in(self, c: Clause) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@c).len() &&
                (@c)[i] === self
        }
    }
    #[predicate]
    pub fn invariant(self, n: Int) -> bool {
        pearlite! {
            @self.idx < n
        }
    }

    #[predicate]
    pub fn sat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            match self.polarity {
                true  =>  (@a[@self.idx] == 1),
                false =>  (@a[@self.idx] == 0),
            }
        }
    }

    #[predicate]
    pub fn unsat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            match self.polarity {
                true  =>  (@a[@self.idx] == 0),
                false =>  (@a[@self.idx] == 1),
            }
        }
    }

    #[predicate]
    pub fn unset_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            @(a)[@self.idx] >= 2
        }
    }

    #[predicate]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! {
            self.sat_inner(@a)
        }
    }

    #[predicate]
    pub fn unset(self, a: Assignments) -> bool {
        pearlite! {
            self.unset_inner(@a)
        }
    }

    #[predicate]
    pub fn unsat(self, a: Assignments) -> bool {
        pearlite! {
            self.unsat_inner(@a)
        }
    }

}

impl Lit {
    #[inline]
    #[requires(self.invariant((@a).len()))]
    #[ensures(result === self.sat(*a))]
    pub fn lit_sat(self, a: &Assignments) -> bool {
        match self.polarity {
            true  =>  (a.0[self.idx] == 1),
            false =>  (a.0[self.idx] == 0),
        }
    }

    #[inline]
    #[requires(self.invariant((@a).len()))]
    #[ensures(result === self.unsat(*a))]
    pub fn lit_unsat(self, a: &Assignments) -> bool {
        match self.polarity {
            true  =>  (a.0[self.idx] == 0),
            false =>  (a.0[self.idx] == 1),
        }
    }

    #[inline]
    #[requires(self.invariant((@a).len()))]
    #[ensures(result === self.unset(*a))]
    pub fn lit_unset(self, a: &Assignments) -> bool {
        a.0[self.idx] >= 2
    }
}