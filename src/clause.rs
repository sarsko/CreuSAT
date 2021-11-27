extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;
use crate::lit::*;
use crate::assignments::*;
use crate::formula::*;
use crate::logic::*;
use crate::ghost::*;
use crate::predicates::*;

pub struct Clause(pub Vec<Lit>);

impl Model for Clause {
    type ModelTy = Seq<Lit>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        self.0.model()
    }
}

impl Clause {
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
    #[ensures(result === sat_clause_inner(@a, self))]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! { sat_clause_inner(@a, self) }
    }

    #[predicate]
    pub fn unknown(self, a: Assignments) -> bool {
        !self.sat(a) && !self.unsat(a)
    }

    #[predicate]
    pub fn contains(self, l: Lit) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@self).len() && (@self)[i] === l
        }
    }

    #[predicate]
    pub fn in_formula(self, f: Formula) -> bool {
        pearlite! { exists<i: Int> 0 <= i && i < (@f.clauses).len() && (@f.clauses)[i] === self }
    }

    #[ensures(result === self.sat(*a))]
    #[requires(self.in_formula(*f))]
    #[requires(f.invariant())]
    #[requires(a.invariant(*f))]
    pub fn is_sat(&self, f: &Formula, a: &Assignments) -> bool {
        let mut i: usize = 0;
        #[invariant(previous, forall<j: Int> 0 <= j && j < @i ==>
            match (@a)[@(@self)[j].idx] {
                AssignedState::Positive => !(@self)[j].polarity,
                AssignedState::Negative => (@self)[j].polarity,
                AssignedState::Unset => true,
            }
        )]
        while i < self.0.len() {
            let lit = self.0[i];
            match a.0[lit.idx]{
            AssignedState::Positive => {
                    if lit.polarity {
                        return true
                    }
                },
                AssignedState::Negative => {
                    if !lit.polarity {
                        return true
                    }
                },
                AssignedState::Unset => {
                }
            }
            i += 1;
        }
        return false;
    }

    #[ensures(result === self.unsat(*a))]
    #[requires(self.in_formula(*f))]
    #[requires(f.invariant())]
    #[requires(a.invariant(*f))]
    pub fn is_unsat(&self, f: &Formula, a: &Assignments) -> bool {
        let mut i: usize = 0;
        //#[invariant(loop_invariant, 0 <= @i && @i <= (@clause).len())]
        #[invariant(previous, forall<j: Int> 0 <= j && j < @i ==>
            match (@a)[@(@self)[j].idx] {
                AssignedState::Positive => !(@self)[j].polarity,
                AssignedState::Negative => (@self)[j].polarity,
                AssignedState::Unset => false,
            }
        )]
        while i < self.0.len() {
            let lit = self.0[i];
            match a.0[lit.idx]{
            AssignedState::Positive => {
                    if lit.polarity {
                        return false
                    }
                },
                AssignedState::Negative => {
                    if !lit.polarity {
                        return false
                    }
                },
                AssignedState::Unset => {
                    return false;
                }
            }
            i += 1;
        }
        return true;
    }
}