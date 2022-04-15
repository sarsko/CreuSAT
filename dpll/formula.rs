extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::lit::*;
use crate::clause::*;
use crate::assignments::*;
use crate::logic::*;
use crate::solver_dpll::*;

pub struct Formula {
    pub clauses: Vec<Clause>,
    pub num_vars: usize,
}

#[derive(Copy, Clone, Eq)]
pub enum SatState {
    Unknown,
    Sat,
    Unsat,
}

impl PartialEq for SatState {
    #[trusted] // OK
    fn eq(&self, other: &Self) -> bool {
        return match (self, other) {
            (SatState::Unknown, SatState::Unknown)  => true,
            (SatState::Sat,     SatState::Sat)      => true,
            (SatState::Unsat,   SatState::Unsat)    => true,
            _ => false,
        };
    }
}

// Predicates
impl Formula {
    #[predicate]
    pub fn invariant(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
                (@self.clauses)[i].invariant(@self.num_vars)
        }
    }

    #[predicate]
    pub fn eventually_sat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<a2 : Seq<AssignedState>> a2.len() === @self.num_vars && compatible_inner(a, a2) && self.sat_inner(a2)
        }
    }

    #[predicate]
    pub fn eventually_sat_complete_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<a2 : Seq<AssignedState>> a2.len() === @self.num_vars && compatible_complete_inner(a, a2) && self.sat_inner(a2)
        }
    }

    #[predicate]
    pub fn eventually_sat_complete(self, a: Assignments) -> bool {
        pearlite! { self.eventually_sat_complete_inner(@a)}
    }

    #[predicate]
    pub fn eventually_sat(self, a: Assignments) -> bool {
        pearlite! { self.eventually_sat_inner(@a)}
    }

    #[predicate]
    pub fn sat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
                (@self.clauses)[i].sat_inner(a)
        }
    }

    #[predicate]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! { 
            self.sat_inner(@a)
        }
    }

    #[predicate]
    pub fn unsat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@(self.clauses)).len() &&
                (@(self.clauses))[i].unsat_inner(a)
        }
    }

    #[predicate]
    pub fn unsat(self, a: Assignments) -> bool {
        pearlite! {
            self.unsat_inner(@a)
        }
    }
}

impl Formula {
    // NONE OF THESE ARE IN USE
    #[trusted] // OK
    #[requires(self.invariant())]
    #[requires(a.invariant(*self))]
    #[ensures(result === self.unsat(*a))]
    pub fn is_unsat(&self, a: &Assignments) -> bool {
        let mut i: usize = 0;
        #[invariant(prev,
            forall<k: Int> 0 <= k && k < @i ==>
            !(@self.clauses)[k].unsat(*a))]
        while i < self.clauses.len() {
            if is_clause_unsat(self, i, a) {
                return true;
            }
            i += 1;
        }
        return false;
    }

    #[trusted] // OK
    #[requires(self.invariant())]
    #[requires(a.invariant(*self))]
    #[ensures(result === self.sat(*a))]
    pub fn is_sat(&self, a: &Assignments) -> bool {
        let mut i: usize = 0;
        #[invariant(prev,
            forall<k: Int> 0 <= k && k < @i ==>
            (@self.clauses)[k].sat(*a))]
        while i < self.clauses.len() {
            if !is_clause_sat(self, i, a) {
                return false;
            }
            i += 1
        }
        return true;
    }

    #[trusted] // OK
    #[requires(self.invariant())]
    #[requires(a.invariant(*self))]
    #[ensures((result === SatState::Sat) === self.sat(*a))]
    #[ensures((result === SatState::Unsat) === self.unsat(*a))]
    #[ensures((result === SatState::Unknown) ==> !a.complete())]
    pub fn eval(&self, a: &Assignments) -> SatState {
        if self.is_sat(a) {
            return SatState::Sat;
        } else if self.is_unsat(a) {
            return SatState::Unsat;
        } else {
            return SatState::Unknown;
        }
    }
}