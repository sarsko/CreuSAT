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
        pearlite! { sat_clause_inner(@  a, self) }
        /*
        pearlite! {
            exists<i: Int> 0 <= i && i < (@self).len() &&
                match (@a)[@(@self)[i].idx] {
                    AssignedState::Positive => (@self)[i].polarity,
                    AssignedState::Negative => !(@self)[i].polarity,
                    AssignedState::Unset => false
                }
        }
        */
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
    pub fn is_unass_in(self, l: Lit, a: Assignments) -> bool {
        pearlite! {
            self.contains(l) && (@a)[@l.idx] === AssignedState::Unset && self.unit(a)
        }
    }

    #[predicate]
    pub fn assign_makes_sat(self, l: Lit, a: Assignments) -> bool {
        pearlite! {
            self.is_unass_in(l, a) ==> sat_clause_inner((@a).set(@l.idx, bool_to_assignedstate(l.polarity)), self)
        }
    }

    #[predicate]
    pub fn assign_reduces(self, l: Lit, a: Assignments) -> bool {
        pearlite! {
            self.is_unass_in(l, a) ==> 
            unassigned_count_clause(@self, (@a).set(@l.idx, bool_to_assignedstate(l.polarity))) === 0
        }
    }

    #[requires(f.invariant())]
    #[requires(a.invariant(*f))]
    #[requires(self.unit(*a))]
    #[requires(forall<i: Int> 0 <= i && i < (@self).len() ==>
        @(@self)[i].idx < (@a).len())] // +requires self in assignments //TODO refactor
    #[ensures((^a).invariant(*f))]
    #[ensures((*a).compatible(^a))]
    #[ensures(self.sat(^a))]
    #[ensures(f.eventually_unsat(*a) ==> f.eventually_unsat(^a))] // Checks out
    #[ensures(f.eventually_sat(^a) ==> f.eventually_sat(*a))] // Checks out
    #[ensures(f.eventually_sat(*a) ==> f.eventually_sat(^a))] // TODO
    #[ensures(f.eventually_unsat(^a) ==> f.eventually_unsat(*a))] // TODO
    pub fn assign_unit(&self, a: &mut Assignments, f: &Formula) {
        let lit = self.get_unit(a, f);
        /*
        proof_assert! {has_to_assign(*self, *a)}
        proof_assert! {
                eventually_sat_formula_inner(@a, *f) ==>
                eventually_sat_formula_inner((@a).set(@lit.idx, bool_to_assignedstate(lit.polarity)), *f)
        }
        proof_assert! {
                eventually_sat_formula_inner(@a, *f) ==>
                not_sat_formula_inner((@a).set(@lit.idx, bool_to_assignedstate(flipbool(lit.polarity))), *f)
        }
        */
        if lit.polarity {
            //proof_assert! {not_sat_clause_inner((@a).set(@lit.idx, AssignedState::Negative), *self)}
            //proof_assert! {!sat_clause_inner((@a).set(@lit.idx, AssignedState::Negative), *self)}
            proof_assert! {self.is_unass_in(lit, *a)}
            proof_assert! {self.assign_makes_sat(lit, *a)}
            proof_assert! {self.assign_reduces(lit, *a)}
            proof_assert! { (@a)[@lit.idx] === AssignedState::Unset }
            proof_assert! {unassigned_count_clause(@self, @a) === 1}
            a.0[lit.idx] = AssignedState::Positive;
            proof_assert! {unassigned_count_clause(@self, @a) === 0}
        } else {
            a.0[lit.idx] = AssignedState::Negative;
        }
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
    #[ensures(self.is_unass_in(result, *a))]
    #[ensures(self.contains(result))]
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