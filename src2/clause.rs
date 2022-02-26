extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;
use crate::lit::*;
use crate::assignments::*;
use crate::formula::*;
use crate::logic::*;

pub struct Clause {
    //pub first: Lit,
    //pub second: Lit,
    pub rest: Vec<Lit>
}

impl Model for Clause {
    type ModelTy = Seq<Lit>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        self.rest.model()//.push(self.first)//.push(self.second)
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

impl Clause {
    // Can be made to a complete eval function if I like
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
        let mut k: usize = 0;
        #[invariant(loop_invariant, 0 <= @i && @i <= (@self).len())]
        #[invariant(unass, @unassigned < 2)] 
        #[invariant(k_is_unass, (@unassigned === 0 || (@a)[@(@self)[@k].idx] === AssignedState::Unset))]
        #[invariant(kk, @unassigned > 0 ==> 
                ((@a)[@(@self)[@k].idx] === AssignedState::Unset))]
        #[invariant(not_sat, forall<j: Int> 0 <= j && j < @i ==>
            match (@a)[@(@self)[j].idx] {
                AssignedState::Positive => !(@self)[j].polarity,
                AssignedState::Negative => (@self)[j].polarity,
                AssignedState::Unset => @unassigned === 1,
            }
        )]
        #[invariant(k_in_bounds, @unassigned === 0 || 0 <= @k && @k < (@self).len())]
        #[invariant(k_only, @unassigned === 1 ==>
                        (forall<j: Int> 0 <= j && j < @i && j != @k ==>
                            !((@a)[@(@self)[j].idx] === AssignedState::Unset))
        )]
        #[invariant(k_unset, @unassigned === 0 ==> @k === 0)]
        while i < self.rest.len() {
            let lit = self.rest[i];
            if lit.lit_sat(a) {
                return false;
            } else if lit.lit_unset(a) {
                if unassigned > 0 {
                    return false;
                }
                k = i;
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
    #[ensures(exists<j: Int> 0 <= j && j < (@self).len() && (@self)[j] === result)]
    #[ensures(@result.idx < (@a).len())]
    #[ensures((@a)[@result.idx] === AssignedState::Unset)]
    pub fn get_unit(&self, a: &Assignments, f: &Formula) -> Lit {
        let mut i: usize = 0;
        #[invariant(not_unset, forall<j: Int> 0 <= j && j < @i ==>
            !((@a)[@(@self)[j].idx] === AssignedState::Unset))]
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