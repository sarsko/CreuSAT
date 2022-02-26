extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;
use crate::lit::*;
use crate::assignments::*;
use crate::formula::*;
use crate::logic::*;
use solver_dpll::bool_to_u8;

pub struct Clause {
    pub first: Lit,
    pub second: Lit,
    pub rest: Vec<Lit>
}

impl Model for Clause {
    type ModelTy = Seq<Lit>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        //self.rest.model().push(self.first).push(self.second)
        self.rest.model()
    }
}

impl Clause {
    #[predicate]
    pub fn vars_in_range(self, n: Int) -> bool {
        pearlite! {
            self.first.invariant(n) &&
            self.second.invariant(n) &&
            forall<i: Int> 0 <= i && i < (@self.rest).len() ==> 
            (@self.rest)[i].invariant(n)
        }
    }
    
    /*
    #[predicate]
    pub fn idxs_in_range(self, n: Int) -> bool {
        pearlite! {
            (0 <= self.first.to_neg_watchidx_logic() && self.first.to_neg_watchidx_logic() < n) &&
            (0 <= self.second.to_neg_watchidx_logic() && self.second.to_neg_watchidx_logic() < n) &&
            forall<i: Int> 0 <= i && i < (@self).len() ==>
                (0 <= ((@self)[i]).to_neg_watchidx_logic() && ((@self)[i]).to_neg_watchidx_logic() < n)
        }
    }
    */

    #[predicate]
    pub fn no_duplicate_indexes(self) -> bool {
        pearlite! {
            !(@self.first.idx === @self.second.idx) &&
            forall<j: Int, k: Int> 0 <= j && j < (@self).len() ==>
                 0 <= k && k < (@self).len() ==> j != k ==> !(@((@self)[k]).idx === @((@self)[j]).idx) && 
                 !(@((@self)[j]).idx === @self.first.idx) &&
                 !(@((@self)[j]).idx === @self.second.idx)
        }
    }

    #[predicate]
    pub fn invariant(self, n: Int) -> bool {
        pearlite! { self.vars_in_range(n) && self.no_duplicate_indexes() }
    }
}


impl Clause {
    #[predicate]
    pub fn first_unit(self, a: Seq<u8>) -> bool {
        pearlite! {
            self.first.unset_u8(a) && self.second.unsat_u8(a) &&
            forall<i: Int> 0 <= i && i < (@self.rest).len() ==>
                (@self.rest)[i].unsat_u8(a)
        }
    }

    #[predicate]
    pub fn second_unit(self, a: Seq<u8>) -> bool {
        pearlite! {
            self.first.unsat_u8(a) && self.second.unset_u8(a) &&
            forall<i: Int> 0 <= i && i < (@self.rest).len() ==>
                (@self.rest)[i].unsat_u8(a)
        }
    }

    #[predicate]
    pub fn unit_in_rest(self, a: Seq<u8>) -> bool {
        pearlite! {
            self.first.unsat_u8(a) && self.second.unsat_u8(a) &&
            exists<i: Int> 0 <= i && i < (@self).len() &&
                ((@self.rest)[i].unset_u8(a) &&
                forall<j: Int> 0 <= j && j < (@self.rest).len() && j != i ==>
                    (@self.rest)[j].unsat_u8(a))
        }
    }

    #[predicate]
    pub fn unit_u8(self, a: Seq<u8>) -> bool {
        pearlite! {
            !self.sat_u8(a) && // This shouldnt be needed tbh
            self.vars_in_range(a.len()) &&
                (self.first_unit(a) || self.second_unit(a) || self.unit_in_rest(a))
        }
    }
    #[predicate]
    pub fn unit(self, a: Assignments) -> bool {
        pearlite! {
            self.unit_u8(@a)
        }
    }

    #[predicate]
    pub fn unsat(self, a: Assignments) -> bool {
        pearlite! {
            self.unsat_u8(@a)
        }
    }

    #[predicate]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! {
            self.sat_u8(@a)
        }
    }

    #[predicate]
    pub fn sat_u8(self, a: Seq<u8>) -> bool {
        pearlite! {
            self.first.sat_u8(a) || self.second.sat_u8(a) ||
            (exists<i: Int> 0 <= i && i < (@self.rest).len() &&
                (@self.rest)[i].sat_u8(a))
        }
    }

    #[predicate]
    pub fn unsat_u8(self, a: Seq<u8>) -> bool {
        pearlite! {
            self.first.unsat_u8(a) && self.second.unsat_u8(a) &&
            (forall<i: Int> 0 <= i && i < (@self.rest).len() ==>
                (@self.rest)[i].unsat_u8(a))
        }
    }

    #[predicate]
    pub fn unknown(self, a: Assignments) -> bool {
        !self.sat(a) && !self.unsat(a)
    }

}

impl Clause {
    // Can be made to a complete eval function if I like
    //#[trusted]
    #[requires(self.invariant((@a).len()))]
    #[requires(f.invariant())]
    #[requires(a.invariant(*f))]
    #[ensures(result ==> self.unit(*a))] 
    //#[ensures(!result ==> !self.unit(*a))]
    //#[ensures(result ==> !self.unsat(*a))] 
    //#[ensures(result ==> !self.sat(*a))] 
    pub fn check_if_unit(&self, a: &Assignments, f: &Formula) -> bool {
        let mut i: usize = 0;
        let mut unassigned: usize = 0;
        if self.first.lit_sat(a) {
            return false;
        } else if self.first.lit_unset(a) {
            unassigned += 1;
        }
        if self.second.lit_sat(a) {
            return false;
        } else if self.second.lit_unset(a) {
            if unassigned > 0 {
                return false;
            }
            unassigned += 1;
        }
        #[invariant(unass, @unassigned < 2)] 
        #[invariant(unass_eq_1, @unassigned === 1 ==>
            ((self.first.unset(*a) && self.second.unsat(*a) &&
                forall<k: Int> 0 <= k && k < @i ==>
                    (@self.rest)[k].unsat(*a))
            ||
            (self.first.unsat(*a) && self.second.unset(*a) &&
                forall<k: Int> 0 <= k && k < @i ==>
                    (@self.rest)[k].unsat(*a))
            ||
            (self.first.unsat(*a) && self.second.unsat(*a) &&
                exists<j : Int> 0 <= j && j < @i &&
                ((@self.rest)[j].unset(*a)  &&
                    forall<k: Int> 0 <= k && k < @i && k != j ==>
                        (@self.rest)[k].unsat(*a))))
        )]
        #[invariant(unass_eq_0, @unassigned === 0 ==>
            (self.first.unsat(*a) && self.second.unsat(*a) &&
                forall<k: Int> 0 <= k && k < @i ==>
                    (@self.rest)[k].unsat(*a))
        )]
        #[invariant(loop_invariant, 0 <= @i && @i <= (@self).len())]
        #[invariant(not_sat, forall<j: Int> 0 <= j && j < @i ==> !(@self)[j].sat(*a))]
        while i < self.rest.len() {
            let lit = self.rest[i];
            if lit.lit_sat(a) {
                return false;
            } else if lit.lit_unset(a) {
                if unassigned > 0 {
                    return false;
                }
                unassigned += 1;
            }
            i += 1;
        }
        if unassigned == 1 {
            true
        } else {
            false
        }
    }

    #[requires(self.unit(*a))]
    #[requires(f.invariant())]
    #[requires(a.invariant(*f))]
    #[ensures(self.first === result || self.second === result ||
        exists<j: Int> 0 <= j && j < (@self).len() && (@self)[j] === result)] // Change to lit in
    #[ensures(@result.idx < (@a).len())]
    #[ensures(@(@a)[@result.idx] >= 2)]
    pub fn get_unit(&self, a: &Assignments, f: &Formula) -> Lit {
        let mut i: usize = 0;
        let res = a.0[self.first.idx];
        if res >= 2 {
            return self.first;
        }         
        let res = a.0[self.second.idx];
        if res >= 2 {
            return self.second;
        } 
        #[invariant(loop_invariant, 0 <= @i && @i <= (@self).len())]
        #[invariant(not_unset, forall<j: Int> 0 <= j && j < @i ==>
            @(@a)[@(@self)[j].idx] < 2)]
        while i < self.rest.len() {
            let lit = self.rest[i];
            let res = a.0[lit.idx];
            if res >= 2 {
                return lit;
            }
            i += 1;
        }
        panic!();
    }
}