extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{assignments::*, clause::*, lit::*, trail::*};

// Logic
impl Lit {
    #[logic]
    pub fn to_watchidx_logic(&self) -> Int {
        pearlite! { @self.idx * 2 + if self.polarity { 0 } else { 1 } }
    }

    #[logic]
    pub fn to_neg_watchidx_logic(&self) -> Int {
        pearlite! { @self.idx * 2 + if self.polarity { 1 } else { 0 } }
    }
}

// Predicates
impl Lit {
    #[predicate]
    pub fn is_opp(self, o: Lit) -> bool {
        pearlite! {
            @self.idx === @o.idx && self.polarity != o.polarity
        }
    }

    #[predicate]
    pub fn lit_in_internal(self, c: Seq<Lit>) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < c.len() &&
                c[i] === self
        }
    }

    #[predicate]
    //#[ensures(result === self.lit_in_internal(@c))]
    pub fn lit_in(self, c: Clause) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@c).len() &&
                (@c)[i] === self
            /*
            exists<i: Int> 0 <= i && i < (@c).len() &&
                (@c)[i].idx === self.idx &&
                (@c)[i].polarity === self.polarity
                */
        }
    }

    #[predicate]
    //#[ensures(result === self.lit_in_internal(@c))]
    pub fn lit_idx_in(self, c: Clause) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@c).len() &&
                (@c)[i].idx === self.idx
            /*
            exists<i: Int> 0 <= i && i < (@c).len() &&
                (@c)[i].idx === self.idx &&
                (@c)[i].polarity === self.polarity
                */
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

    #[predicate]
    pub fn idx_in_trail(self, t: Vec<Step>) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@t).len() &&
                (@t)[i].lit.idx === self.idx
        }
    }
}
