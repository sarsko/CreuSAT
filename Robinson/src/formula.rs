extern crate creusot_contracts;
#[allow(unused)]
use creusot_contracts::{model::*, *};

use crate::{clause::*, solver::*};

#[cfg(creusot)]
use crate::assignments::*;

pub struct Formula {
    pub clauses: Vec<Clause>,
    pub num_vars: usize,
}

#[cfg(creusot)]
impl ShallowModel for Formula {
    type ShallowModelTy = (Seq<Clause>, Int);

    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        (self.clauses.shallow_model(), self.num_vars.shallow_model())
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
            forall<i: Int> 0 <= i && i < (self.clauses@).len() ==>
                (self.clauses@)[i].invariant(self.num_vars@)
        }
    }

    #[predicate]
    pub fn eventually_sat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<a2: Seq<AssignedState>> a2.len() == self.num_vars@ && compatible_inner(a, a2) && self.sat_inner(a2)
        }
    }

    #[predicate]
    pub fn eventually_sat_no_ass(self) -> bool {
        pearlite! { exists<a2: Seq<AssignedState>> self.sat_inner(a2) }
    }

    #[predicate]
    pub fn eventually_sat_complete_no_ass(self) -> bool {
        pearlite! {
            exists<a2: Seq<AssignedState>> a2.len() == self.num_vars@ && complete_inner(a2) && self.sat_inner(a2)
        }
    }

    #[predicate]
    pub fn eventually_sat_complete_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<a2 : Seq<AssignedState>> a2.len() == self.num_vars@ && compatible_complete_inner(a, a2) && self.sat_inner(a2)
        }
    }

    #[predicate]
    pub fn eventually_sat_complete(self, a: Assignments) -> bool {
        pearlite! { self.eventually_sat_complete_inner(a@) }
    }

    #[predicate]
    pub fn eventually_sat(self, a: Assignments) -> bool {
        pearlite! { self.eventually_sat_inner(a@) }
    }

    #[predicate]
    pub fn sat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self.clauses@.len() ==>
                self.clauses@[i].sat_inner(a)
        }
    }

    #[predicate]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! { self.sat_inner(a@) }
    }

    #[predicate]
    pub fn unsat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < self.clauses@.len() &&
                self.clauses@[i].unsat_inner(a)
        }
    }

    #[predicate]
    pub fn unsat(self, a: Assignments) -> bool {
        pearlite! { self.unsat_inner(a@) }
    }

    #[predicate]
    pub fn contains_empty_clause(self) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < self.clauses@.len() &&
             self.clauses@[i]@.len() == 0
        }
    }
}

impl Formula {
    #[cfg_attr(feature = "trust_formula", trusted)]
    #[requires(forall<i: Int> 0 <= i && i < self.clauses@.len() ==>
            self.clauses@[i].vars_in_range(usize::MAX@))]
    #[ensures(match result {
        SatResult::Sat(assn) => { (^self).eventually_sat_no_ass() && formula_sat_inner(self@, assn@) },
        SatResult::Unsat     => { (^self).contains_empty_clause() && !self.eventually_sat_complete_no_ass() },
        SatResult::Unknown   => { (^self).invariant() },
    })]
    #[ensures(self.clauses == (^self).clauses)]
    pub fn check_and_establish_formula_invariant(&mut self) -> SatResult {
        if self.clauses.len() == 0 {
            let a = Vec::new();
            // These just help the proof along.
            proof_assert!(self.sat_inner(a@));
            proof_assert!(self.eventually_sat_no_ass());
            return SatResult::Sat(a);
        }
        let old_self: Ghost<&mut Formula> = ghost!(self);
        let mut i: usize = 0;
        #[invariant(forall<j: Int> 0 <= j && j < i@ ==> self.clauses@[j].invariant(self.num_vars@))]
        #[invariant(forall<j: Int> 0 <= j && j < i@ ==> self.clauses@[j]@.len() > 0)]
        #[invariant(self@.0 == old_self.inner()@.0)]
        #[invariant(self.clauses == old_self.clauses)]
        while i < self.clauses.len() {
            if self.clauses[i].len() == 0 {
                return SatResult::Unsat;
            }
            let new_n = self.clauses[i].check_clause_invariant(self.num_vars);
            if new_n > self.num_vars {
                self.num_vars = new_n;
            }
            i += 1;
        }
        return SatResult::Unknown;
    }
}
