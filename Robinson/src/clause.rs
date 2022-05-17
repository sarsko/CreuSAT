extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::assignments::*;
use crate::formula::*;
use crate::lit::*;
use crate::logic::*;

pub struct Clause {
    pub rest: Vec<Lit>,
}

#[cfg(feature = "contracts")]
impl Model for Clause {
    type ModelTy = Seq<Lit>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        self.rest.model() //.push(self.first)//.push(self.second)
    }
}

impl Clause {
    #[predicate]
    pub fn in_formula(self, f: Formula) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@f.clauses).len() &&
                (@f.clauses)[i] === self
        }
    }

    #[predicate]
    pub fn unit_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            self.vars_in_range(a.len()) &&
                !self.sat_inner(a) &&
                    exists<i: Int> 0 <= i && i < (@self).len() &&
                        (@self)[i].unset_inner(a) &&
                            (forall<j: Int> 0 <= j && j < (@self).len() && j != i ==>
                                !(@self)[j].unset_inner(a))
        }
    }
    #[predicate]
    pub fn unit(self, a: Assignments) -> bool {
        pearlite! {
            self.unit_inner(@a)
        }
    }

    #[predicate]
    pub fn unsat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self).len() ==>
                (@self)[i].unsat_inner(a)
        }
    }

    #[predicate]
    pub fn unsat(self, a: Assignments) -> bool {
        pearlite! {
            self.unsat_inner(@a)
        }
    }

    #[predicate]
    pub fn sat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@self).len() &&
                (@self)[i].sat_inner(a)
        }
    }

    #[predicate]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! {
            self.sat_inner(@a)
        }
    }

    #[predicate]
    pub fn unknown(self, a: Assignments) -> bool {
        !self.sat(a) && !self.unsat(a)
    }

    #[predicate]
    pub fn vars_in_range(self, n: Int) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self).len() ==>
                (@self)[i].invariant(n)
        }
    }

    #[predicate]
    pub fn no_duplicate_indexes(self) -> bool {
        pearlite! {
            forall<j: Int, k: Int> 0 <= j && j < (@self).len() &&
                 k < j ==> !(@(@self)[k].idx === @(@self)[j].idx)
        }
    }

    #[predicate]
    pub fn invariant(self, n: Int) -> bool {
        // Should remove the possibility of empty clauses
        pearlite! { self.vars_in_range(n) && self.no_duplicate_indexes() }
    }
}

//#[derive(Copy, Clone, Eq)]
pub enum ClauseState {
    Sat,
    Unsat,
    Unit,
    Unknown,
}

impl Clause {
    #[inline]
    #[trusted] // TMP
    pub fn clause_from_vec(vec: &Vec<Lit>) -> Clause {
        Clause { rest: vec.clone() }
    }
    //#[trusted] // OK
    #[requires(self.invariant((@a).len()))]
    #[requires(f.invariant())]
    #[requires(a.invariant(*f))]
    #[ensures((result === ClauseState::Sat)     ==> self.sat(*a))]
    #[ensures((result === ClauseState::Unsat)   ==> self.unsat(*a))]
    #[ensures((result === ClauseState::Unit)    ==> self.unit(*a) && !a.complete())]
    #[ensures((result === ClauseState::Unknown) ==> !a.complete())]
    pub fn check_if_unit(&self, a: &Assignments, f: &Formula) -> ClauseState {
        let mut i: usize = 0;
        let mut k: usize = 0;
        let mut unassigned: usize = 0;
        #[invariant(loop_invariant, 0 <= @i && @i <= (@self.rest).len())]
        #[invariant(unass, @unassigned <= 1)]
        #[invariant(k_is_unass, (@unassigned === 0 || (@self)[@k].unset(*a)))]
        #[invariant(kk, @unassigned > 0 ==> (@self)[@k].unset(*a))]
        #[invariant(not_sat, forall<j: Int> 0 <= j && j < @i ==>
            ((@self)[j].unsat(*a) || ((@self)[j].unset(*a) && @unassigned >= 1)))]
        #[invariant(k_in_bounds, @unassigned === 0 || 0 <= @k && @k < (@self).len())]
        #[invariant(k_only, @unassigned === 1 ==> 
            (forall<j: Int> 0 <= j && j < @i && j != @k ==> !(@self)[j].unset(*a)))]
        #[invariant(k_unset, @unassigned === 0 ==> @k === 0)]
        while i < self.rest.len() {
            let lit = self.rest[i];
            if lit.lit_sat(a) {
                return ClauseState::Sat;
            } else if lit.lit_unset(a) {
                // Could make two different check_if_unit functions, one for pre_sat_possible and one for after
                if unassigned > 0 {
                    return ClauseState::Unknown;
                }
                k = i;
                unassigned += 1;
            }
            i += 1;
        }
        if unassigned == 1 {
            ClauseState::Unit
        } else {
            ClauseState::Unsat
        }
    }

    #[trusted] // OK
    #[requires(self.unit(*a))]
    #[requires(f.invariant())]
    #[requires(a.invariant(*f))]
    #[ensures(exists<j: Int> 0 <= j && j < (@self).len() && (@self)[j] === result)]
    #[ensures(@result.idx < (@a).len())]
    #[ensures(unset((@a)[@result.idx]))]
    pub fn get_unit(&self, a: &Assignments, f: &Formula) -> Lit {
        let mut i: usize = 0;
        #[invariant(not_unset, forall<j: Int> 0 <= j && j < @i ==> !(@self)[j].unset(*a))]
        while i < self.rest.len() {
            let lit = self.rest[i];
            if lit.lit_unset(a) {
                return lit;
            }
            i += 1;
        }
        panic!();
    }
}
