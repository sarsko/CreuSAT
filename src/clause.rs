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
pub fn vars_in_range(n: Int, c: Clause) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < (@c).len() ==>
            (0 <= @((@c)[i]).idx && @((@c)[i]).idx < n)
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
            match a[@(@c)[i].idx] {
                AssignedState::Positive => !(@c)[i].polarity,
                AssignedState::Negative => (@c)[i].polarity,
                AssignedState::Unset => false,
            }
    }
}


impl Clause {
    #[predicate]
    pub fn unit(self, a: Assignments) -> bool {
        pearlite! {
            unassigned_count_clause(@self, @a) === 1 && !self.sat(a) && !self.unsat(a) // This should be redundant
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

    #[trusted] // TODO
    #[requires(forall<i: Int> 0 <= i && i < (@self).len() ==>
        @(@self)[i].idx < (@a).len())] // TODO: Refactor
    #[requires(f.invariant())]
    #[requires(a.invariant(*f))]
    #[ensures(result ==> self.unit(*a))] //TODO
    #[ensures(!result ==> !self.unit(*a))] // TODO
    #[ensures(result ==> !self.unsat(*a))] // TODO
    #[ensures(result ==> !self.sat(*a))] // TODO
    pub fn check_if_unit(&self, a: &Assignments, f: &Formula) -> bool {
        let mut i: usize = 0;
        let mut unassigned: usize = 0;
        #[invariant(loop_invariant, 0 <= @i && @i <= (@self).len())]
        #[invariant(unass, @unassigned < 2)] // TODO: Link unassigned with Unset
        //#[invariant(unass2, unassigned_count_clause_partial(@self, @a, @i) < 2)]
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
                    unassigned += 1;
                },
            }
            i += 1;
        }
        if unassigned == 1 {
            true
        } else {
            false
        }
    }

    #[requires(forall<i: Int> 0 <= i && i < (@self).len() ==>
        @(@self)[i].idx < (@a).len())] // +requires self in assignments //TODO refactor
    #[requires(self.unit(*a))]
    #[requires(f.invariant())]
    #[requires(a.invariant(*f))]
    //#[ensures(@result.idx < (@f.clauses).len())]
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
                AssignedState::Unset => {
                    proof_assert! { (@lit.idx < (@a).len())}
                    return lit; },
            }
            i += 1;
        }
        panic!();
    }
}