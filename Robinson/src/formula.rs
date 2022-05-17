extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::assignments::*;
use crate::clause::*;
use crate::lit::*;
use crate::logic::*;
use crate::solver::*;

pub struct Formula {
    pub clauses: Vec<Clause>,
    pub num_vars: usize,
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

