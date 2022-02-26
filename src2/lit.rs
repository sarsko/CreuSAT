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
            match a[@self.idx] {
                AssignedState::Positive => self.polarity,
                AssignedState::Negative => !self.polarity,
                AssignedState::Unset => false
            }
        }
    }

    #[predicate]
    pub fn unsat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            match a[@self.idx] {
                AssignedState::Positive => !self.polarity,
                AssignedState::Negative => self.polarity,
                AssignedState::Unset => false
            }
        }
    }

    #[predicate]
    pub fn unset_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            a[@self.idx] === AssignedState::Unset
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

#[ensures(b ==> result === AssignedState::Positive)]
#[ensures(!b ==> result === AssignedState::Negative)]
pub fn bool_to_assignedstat(b: bool) -> AssignedState {
    if b {
        AssignedState::Positive
    } else {
        AssignedState::Negative
    }
}

impl Lit {
    #[inline]
    #[requires(self.invariant((@a).len()))]
    #[ensures(result === self.sat(*a))]
    pub fn lit_sat(self, a: &Assignments) -> bool {
        match a.0[self.idx] {
            AssignedState::Positive => self.polarity,
            AssignedState::Negative => !self.polarity,
            AssignedState::Unset => false
        }
    }

    #[inline]
    #[requires(self.invariant((@a).len()))]
    #[ensures(result === self.unsat(*a))]
    pub fn lit_unsat(self, a: &Assignments) -> bool {
        match a.0[self.idx] {
            AssignedState::Positive => !self.polarity,
            AssignedState::Negative => self.polarity,
            AssignedState::Unset => false
        }
    }
    
    #[inline]
    #[requires(self.invariant((@a).len()))]
    #[ensures(result === self.unset(*a))]
    pub fn lit_unset(self, a: &Assignments) -> bool {
        match a.0[self.idx] {
            AssignedState::Unset => true,
            _ => false
        }
    }
}