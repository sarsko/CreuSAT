extern crate creusot_contracts;
#[allow(unused)]
use creusot_contracts::std::*;
#[allow(unused)]
use creusot_contracts::*;

use crate::{assignments::*, formula::*, lit::*};

#[cfg(feature = "contracts")]
use crate::logic::*;

pub struct Clause {
    pub rest: Vec<Lit>,
}

#[cfg(feature = "contracts")]
impl Model for Clause {
    type ModelTy = Seq<Lit>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        self.rest.model()
    }
}

impl Clause {
    #[predicate]
    pub fn in_formula(self, f: Formula) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@f.clauses).len() &&
                (@f.clauses)[i] == self
        }
    }

    #[predicate]
    pub fn unit_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            self.vars_in_range(a.len())
            && !self.sat_inner(a)
            && exists<i: Int> 0 <= i && i < (@self).len() && (@self)[i].unset_inner(a)
            && (forall<j: Int> 0 <= j && j < (@self).len() && j != i ==> !(@self)[j].unset_inner(a))
        }
    }
    #[predicate]
    pub fn unit(self, a: Assignments) -> bool {
        pearlite! { self.unit_inner(@a) }
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
        pearlite! { self.unsat_inner(@a) }
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
        pearlite! { self.sat_inner(@a) }
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
                 0 <= k && k < j ==> !((@self)[k].index_logic() == (@self)[j].index_logic())
        }
    }

    #[predicate]
    pub fn invariant(self, n: Int) -> bool {
        self.vars_in_range(n) //&& self.no_duplicate_indexes()
    }
}

pub enum ClauseState {
    Sat,
    Unsat,
    Unit,
    Unknown,
}

impl Clause {
    #[inline]
    pub fn clause_from_vec(vec: Vec<Lit>) -> Clause {
        Clause { rest: vec }
    }

    #[cfg_attr(feature = "trust_clause", trusted)]
    #[requires(self.invariant((@a).len()))]
    #[requires(_f.invariant())]
    #[requires(a.invariant(*_f))]
    #[ensures((result == ClauseState::Sat)     ==> self.sat(*a))]
    #[ensures((result == ClauseState::Unsat)   ==> self.unsat(*a))]
    #[ensures((result == ClauseState::Unit)    ==> self.unit(*a) && !a.complete())]
    #[ensures((result == ClauseState::Unknown) ==> !a.complete())]
    pub fn check_if_unit(&self, a: &Assignments, _f: &Formula) -> ClauseState {
        let mut i: usize = 0;
        let mut _k: usize = 0; // _k is the "ghost" index of the unset literal
        let mut unassigned: usize = 0;
        #[invariant(loop_invariant, 0 <= @i && @i <= (@self.rest).len())]
        #[invariant(unass, @unassigned <= 1)]
        #[invariant(k_is_unass, (@unassigned == 0 || (@self)[@_k].unset(*a)))]
        #[invariant(kk, @unassigned > 0 ==> (@self)[@_k].unset(*a))]
        #[invariant(not_sat, forall<j: Int> 0 <= j && j < @i ==>
            ((@self)[j].unsat(*a) || ((@self)[j].unset(*a) && @unassigned >= 1)))]
        #[invariant(k_in_bounds, @unassigned == 0 || 0 <= @_k && @_k < (@self).len())]
        #[invariant(k_only, @unassigned == 1 ==>
            (forall<j: Int> 0 <= j && j < @i && j != @_k ==> !(@self)[j].unset(*a)))]
        #[invariant(k_unset, @unassigned == 0 ==> @_k == 0)]
        while i < self.rest.len() {
            let lit = self.rest[i];
            if lit.lit_sat(a) {
                return ClauseState::Sat;
            } else if lit.lit_unset(a) {
                // Could make two different check_if_unit functions, one for pre_sat_possible and one for after
                if unassigned > 0 {
                    return ClauseState::Unknown;
                }
                _k = i;
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

    #[cfg_attr(feature = "trust_clause", trusted)]
    #[requires(self.unit(*a))]
    #[requires(_f.invariant())]
    #[requires(a.invariant(*_f))]
    #[ensures(exists<j: Int> 0 <= j && j < (@self).len() && (@self)[j] == result)]
    #[ensures(result.index_logic() < (@a).len())]
    #[ensures(unset((@a)[result.index_logic()]))]
    pub fn get_unit(&self, a: &Assignments, _f: &Formula) -> Lit {
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

    #[cfg_attr(feature = "trust_clause", trusted)]
    #[requires(self.vars_in_range(@usize::MAX))]
    #[ensures(self.invariant(@result))]
    pub fn check_clause_invariant(&self, n: usize) -> usize {
        let mut i: usize = 0;
        let mut new_n = n;
        #[invariant(inv, forall<j: Int> 0 <= j && j < @i ==> (@self)[j].invariant(@new_n))]
        #[invariant(new_n_inv, @new_n >= @n)]
        while i < self.len() {
            if !self.rest[i].check_lit_invariant(new_n) {
                new_n = self.rest[i].idx + 1;
            }
            i += 1;
        }
        /*
        if self.no_duplicates() {
            return true;
        }
        */
        new_n
    }

    #[cfg_attr(feature = "trust_clause", trusted)]
    #[ensures(result == self.no_duplicate_indexes())]
    pub fn no_duplicates(&self) -> bool {
        let mut i: usize = 0;
        #[invariant(no_dups,
            forall<j: Int, k: Int> 0 <= j && j < @i &&
             0 <= k && k < j ==> (@self)[j].idx != (@self)[k].idx)]
        while i < self.rest.len() {
            let lit1 = self.rest[i];
            let mut j: usize = 0;
            #[invariant(inv, forall<k: Int> 0 <= k && k < @j ==> lit1.idx != (@self)[k].idx)]
            while j < i {
                let lit2 = self.rest[j];
                if lit1.idx == lit2.idx {
                    return false;
                }
                j += 1;
            }
            i += 1;
        }
        return true;
    }

    #[inline(always)]
    #[cfg_attr(feature = "trust_clause", trusted)]
    #[ensures(@result == (@self).len())]
    pub fn len(&self) -> usize {
        self.rest.len()
    }
}
