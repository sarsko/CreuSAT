extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::ghost;
use crate::lit::*;
use crate::clause::*;
use crate::assignments::*;
use crate::logic::*;
use crate::predicates::*;
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
    #[trusted]
    fn eq(&self, other: &Self) -> bool {
        return match (self, other) {
            (SatState::Unknown, SatState::Unknown) => true,
            (SatState::Sat, SatState::Sat) => true,
            (SatState::Unsat, SatState::Unsat) => true,
            _ => false,
        };
    }
}

// Predicates
impl Formula {
    #[predicate]
    pub fn invariant(self) -> bool {
        pearlite! {
            (forall<i: Int> 0 <= i && i < (@(self.clauses)).len() ==>
            vars_in_range(@(self.num_vars), ((@(self.clauses))[i])))
        }
    }

    #[predicate]
    pub fn eventually_sat(self, a: Assignments) -> bool {
        pearlite! { eventually_sat_formula_inner(@a, self)}
    }

    #[predicate]
    pub fn eventually_unsat(self, a: Assignments) -> bool {
        pearlite! { eventually_unsat_formula_inner(@a, self) }
    }

    #[predicate]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@(self.clauses)).len() ==>
            (@(self.clauses))[i].sat(a)
        }
    }

    #[predicate]
    pub fn unsat(self, a: Assignments) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@(self.clauses)).len() &&
            (@(self.clauses))[i].unsat(a)
        }
    }
}

impl Formula {
    #[trusted] // TMP, PASSES
    #[requires(self.invariant())]
    #[requires(a.invariant(*self))]
    #[ensures(result === self.sat(*a))]
    pub fn is_sat(&self, a: &Assignments) -> bool {
        let mut i: usize = 0;
        #[invariant(prev,
            forall<k: Int> 0 <= k && k < @i ==>
            (@self.clauses)[k].sat(*a))]
        while i < self.clauses.len() {
            if !self.clauses[i].is_sat(self, a) {
                return false;
            }
            i += 1
        }
        return true;
    }

    #[trusted] // TMP, PASSES
    #[requires(self.invariant())]
    #[requires(a.invariant(*self))]
    #[ensures(result === self.unsat(*a))]
    pub fn is_unsat(&self, a: &Assignments) -> bool {
        let mut i: usize = 0;
        #[invariant(prev,
            forall<k: Int> 0 <= k && k < @i ==>
            !(@self.clauses)[k].unsat(*a))]
        while i < self.clauses.len() {
            if self.clauses[i].is_unsat(self, a) {
                return true;
            }
            i += 1;
        }
        return false;
    }

    #[trusted] // TMP, PASSES
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