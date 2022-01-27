extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;
use crate::lit::*;
use crate::assignments::*;
use crate::formula::*;
use crate::logic::*;
use crate::ghost::*;

pub struct Clause(pub Vec<Lit>);

impl Model for Clause {
    type ModelTy = Seq<Lit>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        self.0.model()
    }
}


#[predicate]
pub fn sat_clause_inner(a: Seq<AssignedState>, c: Clause) -> bool {
    pearlite! {
        exists<i: Int> 0 <= i && i < (@c).len() &&
            match a[@(@c)[i].idx] {
                AssignedState::Positive => (@c)[i].polarity,
                AssignedState::Negative => !(@c)[i].polarity,
                AssignedState::Unset => false,
            }
    }
}


#[predicate]
pub fn not_sat_clause_inner(a: Seq<AssignedState>, c: Clause) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < (@c).len() ==>
        /*
            (!(a[@(@c)[i].idx] === AssignedState::Unset) &&
                !(a[@(@c)[i].idx] === bool_to_assignedstate((@c)[i].polarity)))
                */
            match a[@(@c)[i].idx] {
                AssignedState::Positive => !(@c)[i].polarity,
                AssignedState::Negative => (@c)[i].polarity,
                AssignedState::Unset => false,
            }
    }
}

#[predicate]
pub fn unit_inner(a: Seq<AssignedState>, c: Clause) -> bool {
    pearlite! {
        c.vars_in_range(a.len()) &&
            !sat_clause_inner(a, c) && 
                exists<i: Int> 0 <= i && i < (@c).len() &&
                    a[@(@c)[i].idx] === AssignedState::Unset && 
                        (forall<j: Int> 0 <= j && j < (@c).len() && j != i ==>
                            !(a[@(@c)[j].idx] === AssignedState::Unset))
    }
}

impl Clause {
    #[predicate]
    pub fn unit(self, a: Assignments) -> bool {
        pearlite! {
            unit_inner(@a, self)
        }
    }

    #[predicate]
    pub fn unsat(self, a: Assignments) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self).len() ==>
                match (@a)[@(@self)[i].idx] {
                    AssignedState::Positive => !(@self)[i].polarity,
                    AssignedState::Negative => (@self)[i].polarity,
                    AssignedState::Unset => false,
                }
        }
    }

    #[predicate]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@self).len() &&
                match (@a)[@(@self)[i].idx] {
                    AssignedState::Positive => (@self)[i].polarity,
                    AssignedState::Negative => !(@self)[i].polarity,
                    AssignedState::Unset => false
                }
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
                (0 <= @((@self)[i]).idx && @((@self)[i]).idx < n)
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
        pearlite! { self.vars_in_range(n) && self.no_duplicate_indexes() }
    }
}

impl Clause {
    #[trusted] // TODO
    #[requires(forall<i: Int> 0 <= i && i < (@self).len() ==>
        @(@self)[i].idx < (@a).len())] // TODO: Refactor
    #[requires(f.invariant())]
    #[requires(a.invariant(*f))]
    #[ensures(result ==> self.unit(*a))] //TODO
    //#[ensures(!result ==> !self.unit(*a))] // TODO
    //#[ensures(result ==> !self.unsat(*a))] // TODO
    //#[ensures(result ==> !self.sat(*a))] // TODO
    pub fn check_if_unit(&self, a: &Assignments, f: &Formula) -> bool {
        let mut i: usize = 0;
        let mut unassigned: usize = 0;
        let mut k: usize = 0;
        #[invariant(loop_invariant, 0 <= @i && @i <= (@self).len())]
        #[invariant(unass, @unassigned < 2)] // TODO: Link unassigned with Unset
        //#[invariant(unass2, unassigned_count_clause_partial(@self, @a, @i) < 2)]

        /*
        c.vars_in_range(a.len()) &&
            !sat_clause_inner(a, c) && 
                exists<i: Int> 0 <= i && i < (@c).len() &&
                    a[@(@c)[i].idx] === AssignedState::Unset && 
                        (forall<j: Int> 0 <= j && j < (@c).len() && j != i ==>
                            !(a[@(@c)[j].idx] === AssignedState::Unset))
                            */
        
        #[invariant(is_unit, (forall<j: Int> 0 <= j && j < @i && j != @k ==>
                !((@a)[@(@self)[j].idx] === AssignedState::Unset))
        )]
        #[invariant(k_is_unass, (@k === 0 || (@a)[@(@self)[@k].idx] === AssignedState::Unset))]
        #[invariant(k2, @unassigned > 0 ==> exists<j: Int> 0 <= j && j < @i ==>
                ((@a)[@(@self)[j].idx] === AssignedState::Unset))]
        while i < self.0.len() {
            let lit = self.0[i];
            let res = a.0[lit.idx];
            match res {
                AssignedState::Positive => {
                    if lit.polarity {
                        return false;
                    }
                },
                AssignedState::Negative => {
                    if !lit.polarity {
                        return false;
                    }
                },
                AssignedState::Unset => {
                    if unassigned >= 1 {
                        return false;
                    }
                    k = i;
                    //proof_assert! { (@a)}
                    unassigned += 1;
                },
            }
            i += 1;
        }
        if unassigned == 1 {
            //proof_assert! { self.vars_in_range((@a).len()) }
            proof_assert! { !sat_clause_inner(@a, *self) }
            proof_assert! {
                exists<i: Int> 0 <= i && i < (@self).len() &&
                    (@a)[@(@self)[i].idx] === AssignedState::Unset
            }
            proof_assert! {
                exists<i: Int> 0 <= i && i < (@self).len() &&
                    (@a)[@(@self)[i].idx] === AssignedState::Unset && 
                        (forall<j: Int> 0 <= j && j < (@self).len() && j != i ==>
                            !((@a)[@(@self)[j].idx] === AssignedState::Unset))
            }
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
        #[invariant(loop_invariant, 0 <= @i && @i <= (@self).len())]
        #[invariant(not_unset, forall<j: Int> 0 <= j && j < @i ==>
            !((@a)[@(@self)[j].idx] === AssignedState::Unset))]
        while i < self.0.len() {
            let lit = self.0[i];
            let res = a.0[lit.idx];
            match res {
                AssignedState::Positive => {},
                AssignedState::Negative => {},
                AssignedState::Unset => { return lit; },
            }
            i += 1;
        }
        panic!();
    }
}