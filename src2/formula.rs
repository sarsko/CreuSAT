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
    fn eq(&self, other: &Self) -> bool {
        return match (self, other) {
            (SatState::Unknown, SatState::Unknown) => true,
            (SatState::Sat, SatState::Sat) => true,
            (SatState::Unsat, SatState::Unsat) => true,
            _ => false,
        };
    }
}


#[predicate]
pub fn eventually_sat_complete_formula_inner(a: Seq<u8>, f: Formula) -> bool {
    pearlite! {
        exists<a2 : Seq<u8>> a2.len() === @f.num_vars && compatible_complete_inner(a, a2) && f.sat_u8(a2)//sat_formula_inner(a2, f)
    }
}

#[predicate]
pub fn eventually_sat_formula_inner_old(a: Seq<u8>, f: Formula) -> bool {
    pearlite! {
        exists<a2 : Seq<u8>> a2.len() === @f.num_vars && compatible_inner(a, a2) && sat_formula_inner(a2, f)
    }
}

#[predicate]
pub fn eventually_sat_formula_inner(a: Seq<u8>, f: Formula) -> bool {
    pearlite! {
        exists<a2 : Seq<u8>> a2.len() === @f.num_vars && compatible_inner(a, a2) && f.sat_u8(a2)
    }
}


#[predicate]
pub fn not_sat_formula_inner(a: Seq<u8>, f: Formula) -> bool {
    pearlite! {
        exists<i: Int> 0 <= i && i < (@f.clauses).len() &&
        //not_sat_clause_inner(a, (@f.clauses)[i])
        !(@f.clauses)[i].sat_u8(a)
    }
}

#[predicate]
pub fn clause_in_formula(c: Clause, f: Formula) -> bool {
    pearlite! {
        exists<i: Int> 0 <= i && i < (@f.clauses).len() &&
        (@f.clauses)[i] === c
    }
}

#[predicate]
pub fn sat_formula_inner(a: Seq<u8>, f: Formula) -> bool {
    pearlite! {
            forall<i: Int> 0 <= i && i < (@f.clauses).len() ==>
            (@f.clauses)[i].sat_u8(a)
            //sat_clause_inner(a, (@f.clauses)[i])
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
    pub fn eventually_sat_complete(self, a: Assignments) -> bool {
        pearlite! { eventually_sat_complete_formula_inner(@a, self)}
    }

    #[predicate]
    pub fn eventually_sat(self, a: Assignments) -> bool {
        pearlite! { eventually_sat_formula_inner(@a, self)}
    }

    #[predicate]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! { 
            forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
                (@self.clauses)[i].sat(a)
        }
    }

    #[predicate]
    pub fn unsat(self, a: Assignments) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@self.clauses).len() &&
                (@self.clauses)[i].unsat(a)
        }
    }

    #[predicate]
    pub fn sat_u8(self, a: Seq<u8>) -> bool {
        pearlite! { 
            forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
                (@self.clauses)[i].sat_u8(a)
        }
    }

    #[predicate]
    pub fn unsat_u8(self, a: Seq<u8>) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@self.clauses).len() &&
                (@self.clauses)[i].unsat_u8(a)
        }
    }
}

impl Formula {
    #[requires(self.invariant())]
    #[requires(a.invariant(*self))]
    #[ensures(result === self.unsat(*a))]
    pub fn is_unsat(&self, a: &Assignments) -> bool {
        let mut i: usize = 0;
        #[invariant(prev,
            forall<k: Int> 0 <= k && k < @i ==>
            !(@self.clauses)[k].unsat(*a))]
        #[invariant(loop_invariant, 0 <= @i && @i <= (@self.clauses).len())]
        while i < self.clauses.len() {
            if is_clause_unsat(self, i, a) {
                return true;
            }
            i += 1;
        }
        return false;
    }

    #[requires(self.invariant())]
    #[requires(a.invariant(*self))]
    #[ensures(result === self.sat(*a))]
    pub fn is_sat(&self, a: &Assignments) -> bool {
        let mut i: usize = 0;
        #[invariant(prev,
            forall<k: Int> 0 <= k && k < @i ==>
                (@self.clauses)[k].sat(*a)
        )]
        while i < self.clauses.len() {
            if !is_clause_sat(self, i, a) {
                return false;
            }
            i += 1
        }
        return true;
    }

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