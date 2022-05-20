extern crate creusot_contracts;
#[allow(unused)]
use creusot_contracts::std::*;
#[allow(unused)]
use creusot_contracts::*;

use crate::{clause::*, solver::*};

#[cfg(feature = "contracts")]
use crate::assignments::*;

pub struct Formula {
    pub clauses: Vec<Clause>,
    pub num_vars: usize,
}

#[cfg(feature = "contracts")]
impl Model for Formula {
    type ModelTy = (Seq<Clause>, Int);

    #[logic]
    fn model(self) -> Self::ModelTy {
        (self.clauses.model(), self.num_vars.model())
    }
}

#[predicate]
pub fn formula_sat_inner(f: (Seq<Clause>, Int), a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < f.0.len() ==>
            f.0[i].sat_inner(a)
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
            exists<a2 : Seq<AssignedState>> a2.len() == @self.num_vars && compatible_inner(a, a2) && self.sat_inner(a2)
        }
    }

    #[predicate]
    pub fn eventually_sat_no_ass(self) -> bool {
        pearlite! {
            exists<a2 : Seq<AssignedState>> self.sat_inner(a2)
        }
    }

    #[predicate]
    pub fn eventually_sat_complete_no_ass(self) -> bool {
        pearlite! {
            exists<a2 : Seq<AssignedState>> a2.len() == @self.num_vars && complete_inner(a2) && self.sat_inner(a2)
        }
    }

    #[predicate]
    pub fn eventually_sat_complete_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<a2 : Seq<AssignedState>> a2.len() == @self.num_vars && compatible_complete_inner(a, a2) && self.sat_inner(a2)
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

    #[predicate]
    pub fn contains_empty_clause(self) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@self.clauses).len() &&
             (@(@self.clauses)[i]).len() == 0
        }
    }
}

impl Formula {
    #[cfg_attr(feature = "trust_formula", trusted)]
    #[ensures(match result {
        SatResult::Sat(assn) => { self.eventually_sat_no_ass() && formula_sat_inner(@self, @assn) },
        SatResult::Unsat     => { self.contains_empty_clause() },
        SatResult::Unknown   => { self.invariant() && 0 < @self.num_vars && @self.num_vars < @usize::MAX/2 },
        SatResult::Err       => { true },
    })]
    pub fn check_formula_invariant(&self) -> SatResult {
        if self.num_vars >= usize::MAX / 2 {
            return SatResult::Err;
        }
        if self.clauses.len() == 0 {
            return SatResult::Sat(Vec::new());
        }
        if self.num_vars == 0 {
            return SatResult::Err; // We have no vars but more than 0 clauses -> error.
        }
        let mut i: usize = 0;
        #[invariant(inv, forall<j: Int> 0 <= j && j < @i ==> (@self.clauses)[j].invariant(@self.num_vars))]
        #[invariant(inv, forall<j: Int> 0 <= j && j < @i ==> (@(@self.clauses)[j]).len() > 0)]
        while i < self.clauses.len() {
            if !self.clauses[i].check_clause_invariant(self.num_vars) {
                return SatResult::Err;
            }
            if self.clauses[i].len() == 0 {
                return SatResult::Unsat;
            }
            i += 1;
        }
        return SatResult::Unknown;
    }
}
