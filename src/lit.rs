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

#[predicate]
pub fn lit_sat(l: Lit, a: Seq<AssignedState>) -> bool {
    pearlite! {
        if a[@l.idx] === AssignedState::Unset {
            false
        } else if a[@l.idx] === AssignedState::Positive && l.polarity {
            true
        } else if a[@l.idx] === AssignedState::Negative && !l.polarity {
            true
        } else {
            false
        }

        /*
        match a[@l.idx] {
            AssignedState::Positive => l.polarity,
            AssignedState::Negative => !l.polarity,
            AssignedState::Unset => false
        }
        */
    }
}

// Predicates
impl Lit {
    #[predicate]
    pub fn lit_in(self, c: Clause) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@c).len() ==>
                (@c)[i] === self
        }
    }

    #[predicate]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! {
            match (@a)[@self.idx] {
                AssignedState::Positive => self.polarity,
                AssignedState::Negative => !self.polarity,
                AssignedState::Unset => false
            }
        }
    }
}

impl Lit { }