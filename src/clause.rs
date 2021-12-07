extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;
use crate::lit::*;
use crate::assignments::*;
use crate::formula::*;
use crate::logic::*;
use crate::ghost;
use crate::predicates::*;

pub struct Clause(pub Vec<Lit>);

impl Model for Clause {
    type ModelTy = Seq<Lit>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        self.0.model()
    }
}

#[predicate]
pub fn clause_sat(c: Seq<Lit>, a: Seq<AssignedState>) -> bool {
    /*
    pearlite! {
        exists<i: Int> 0 <= i && i < c.len() &&
            match a[@c[i].idx] {
                AssignedState::Positive => c[i].polarity,
                AssignedState::Negative => !c[i].polarity,
                AssignedState::Unset => false,
            }
    }
    */
    pearlite! {
        exists<i: Int> 0 <= i && i < c.len() &&
            lit_sat(c[i], a)
    }
}

#[logic]
pub fn clause_unsat(c: Seq<Lit>, a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < c.len() ==>
            match (a)[@c[i].idx] {
                AssignedState::Positive => !c[i].polarity,
                AssignedState::Negative => c[i].polarity,
                AssignedState::Unset => false,
            }
    }
}

#[predicate]
pub fn unit_internal(c: Seq<Lit>, a: Seq<AssignedState>) -> bool {
    pearlite! {
        unassigned_count_clause(c, a) === 1 && !clause_sat(c, a) //&& !self.unsat(a) // This should be redundant
    }
}

#[logic]
pub fn is_unass_in(c: Seq<Lit>, l: Lit, a: Seq<AssignedState>) -> bool {
    pearlite! {
        contains(c, l) && a[@l.idx] === AssignedState::Unset && unit_internal(c, a)
    }
}

#[predicate]
pub fn contains(c: Seq<Lit>, l: Lit) -> bool {
    pearlite! {
        exists<i: Int> 0 <= i && i < c.len() && c[i] === l
    }
}

// Predicates
impl Clause {
    #[predicate]
    pub fn unit(self, a: Assignments) -> bool {
        pearlite!{ unit_internal(@self, @a) }
        /*
        pearlite! {
            unassigned_count_clause(@self, @a) === 1 && !self.sat(a) //&& !self.unsat(a) // This should be redundant
        }
        */
    }

    #[predicate]
    pub fn unsat(self, a: Assignments) -> bool {
        pearlite! { clause_unsat(@self, @a) }
    }

    #[predicate]
    #[ensures(result === clause_sat(@self, @a))]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! { clause_sat(@self, @a) }
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

    #[predicate]
    pub fn is_unass_in(self, l: Lit, a: Assignments) -> bool {
        pearlite! { is_unass_in(@self, l, @a) }
    }
}


impl Clause {
    #[trusted] // TMP, PASSES
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

    #[trusted] // TMP, PASSES
    #[ensures(result === self.unsat(*a))]
    #[requires(self.in_formula(*f))]
    #[requires(f.invariant())]
    #[requires(a.invariant(*f))]
    pub fn is_unsat(&self, f: &Formula, a: &Assignments) -> bool {
        let mut i: usize = 0;
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

    #[trusted] // TODO
    #[requires(forall<i: Int> 0 <= i && i < (@self).len() ==>
        @(@self)[i].idx < (@a).len())] // TODO: Refactor
    #[requires(f.invariant())]
    #[requires(a.invariant(*f))]
    #[ensures(!result ==> !self.unit(*a))] // TODO
    #[ensures(result ==> !self.unsat(*a))] // TODO
    #[ensures(result ==> self.unit(*a))] //TODO
    #[ensures(result ==> !self.sat(*a))] 
    pub fn check_if_unit(&self, a: &Assignments, f: &Formula) -> bool {
        let mut i: usize = 0;
        let mut unassigned: usize = 0;
        #[invariant(loop_invariant, 0 <= @i && @i <= (@self).len())]
        #[invariant(unass, @unassigned <= 2)] // TODO: Link unassigned with Unset
        #[invariant(unass, @unassigned <= (@self).len())]
        #[invariant(unass2, unassigned_count_clause_partial(@self, @a, @i) === @unassigned)]
        #[invariant(previous, forall<j: Int> 0 <= j && j < @i ==>
            match (@a)[@(@self)[j].idx] {
                AssignedState::Positive => !(@self)[j].polarity,
                AssignedState::Negative => (@self)[j].polarity,
                AssignedState::Unset => true,
            }
        )]
        while i < self.0.len() {
            let lit = self.0[i];
            let res = a.0[lit.idx];
            let old_unassigned = Ghost::record(&unassigned);
            match res {
                AssignedState::Positive => {
                    if lit.polarity {
                        //proof_assert! { self.sat(*a) }
                        return false;
                    }
                    proof_assert! { @@old_unassigned === @unassigned } 
                },
                AssignedState::Negative => {
                    if !lit.polarity {
                        //proof_assert! { self.sat(*a) }
                        return false;
                    }
                    proof_assert! { @@old_unassigned === @unassigned } 
                },
                AssignedState::Unset => {
                    unassigned += 1;
                    //proof_assert! { unassigned_count_clause_partial(@self, @a, @i) === @unassigned }
                    if unassigned > 1 {
                        //proof_assert! {unassigned_count_clause(@self, @a) > 1}
                        return false;
                    }
                    proof_assert! { @@old_unassigned + 1 === @unassigned } 
                },
            }
            /*
            proof_assert! {
                match res {
                    AssignedState::Positive => @@old_unassigned === @unassigned,
                    AssignedState::Negative => @unassigned === @@old_unassigned,
                    AssignedState::Unset => (@@old_unassigned === @unassigned + 300), // Funky
                }
            }
            */
            i += 1;
        }
        proof_assert! { !self.sat(*a) }
        if unassigned == 1 {
            proof_assert! {unassigned_count_clause(@self, @a) === 1}
            //proof_assert! {!self.unsat(*a)}
            true
        } else {
            //proof_assert! { self.unsat(*a) }
            false
        }
    }

    #[requires(forall<i: Int> 0 <= i && i < (@self).len() ==>
        @(@self)[i].idx < (@a).len())] // +requires self in assignments //TODO refactor
    #[requires(self.unit(*a))]
    #[requires(f.invariant())]
    #[requires(a.invariant(*f))]
    #[ensures(is_unass_in(@self, result, @a))]
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