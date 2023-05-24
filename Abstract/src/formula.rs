extern crate creusot_contracts;

use creusot_contracts::logic::FSet;
use creusot_contracts::{std::clone::Clone, std::*, vec, *};

//use crate::assignments::AssignedState;
use crate::{assignments::*, clause::*, clause_allocator::*, lit::*};
use crate::cref::cref_invariant;

pub struct Formula {
    pub(crate) formula: FSet<ClauseFSet>,
    pub(crate) num_vars: Int,
}

/*
#[logic]
#[variant(just.len() - ix)]
#[requires(ix >= 0)]
#[requires(forall<i: _> 0 <= i && i < just.len() ==> @just[i] < (self@.assignments).len())]
#[ensures(forall<a: _> result.contains(a) ==> exists<i: _> 0 <= i && i < (self@.assignments).len() && a == (self@.assignments)[i].term_value())]
#[ensures(forall<a: _> result.contains(a) ==> exists<i: _> ix <= i && i < just.len() && a == (self@.assignments)[@just[i]].term_value())]
#[ensures(forall<i: _ > ix <= i && i < just.len() ==> result.contains((self@.assignments)[@just[i]].term_value()))]
pub fn abs_just_inner(self, just: Seq<usize>, ix: Int) -> FSet<(theory::Term, theory::Value)> {
    if ix < just.len() {
        let set = self.abs_just_inner(just, ix + 1);
        let a = (self.assignments.model())[just[ix].model()];
        set.insert((a.term.model(), a.val.model()))
    } else {
        FSet::EMPTY
    }
}
*/

impl Formula {
    // TODO: Look at actually implementing from
    // TODO: Have crefs be a CRefManager instead, I think we always get from it
    #[logic]
    #[requires(clause_allocator.invariant())]
    #[requires(forall<i: Int> 0 <= i && i < crefs.len() ==>
                cref_invariant(crefs[i], clause_allocator, num_vars))] // CRefManager.invariant unwrapped -> TODO: refactor?
    #[ensures(result.num_vars == num_vars)]
    #[ensures(forall<i: Int> 0 <= i && i < crefs.len() ==> exists<c: _> result.formula.contains(c) && clause_allocator.get_clause_fset(crefs[i]) == c)]
    #[ensures(forall<c: _> result.formula.contains(c) ==> exists<i: Int> 0 <= i && i < crefs.len() && clause_allocator.get_clause_fset(crefs[i]) == c)]
    pub(crate) fn from(crefs: Seq<Int>, clause_allocator: ClauseAllocatorModel, num_vars: Int) -> Formula {
        Formula { formula: Formula::from_internal(crefs, clause_allocator, 0, num_vars), num_vars }
    }

    #[logic]
    fn insert(self, clause: ClauseFSet) -> Formula {
        Formula { formula: self.formula.insert(clause), num_vars: self.num_vars }
    }

    #[logic]
    #[variant(crefs.len() - idx)]
    #[requires(idx >= 0)]
    #[requires(clause_allocator.invariant())]
    #[requires(forall<i: Int> 0 <= i && i < crefs.len() ==>
                cref_invariant(crefs[i], clause_allocator, _num_vars))] // CRefManager.invariant unwrapped -> TODO: refactor?
    #[ensures(forall<i: Int> idx <= i && i < crefs.len() ==> exists<c: _> result.contains(c) && clause_allocator.get_clause_fset(crefs[i]) == c)]
    #[ensures(forall<c: _> result.contains(c) ==> exists<i: Int> idx <= i && i < crefs.len() && clause_allocator.get_clause_fset(crefs[i]) == c)]
    fn from_internal(
        crefs: Seq<Int>, clause_allocator: ClauseAllocatorModel, idx: Int, _num_vars: Int,
    ) -> FSet<ClauseFSet> {
        pearlite! {
            if idx < crefs.len() {
                let set = Formula::from_internal(crefs, clause_allocator, idx + 1, _num_vars);
                let clause = clause_allocator.get_clause_fset(crefs[idx]);
                set.insert(clause)
            } else {
                FSet::EMPTY
            }
        }
    }

    #[predicate]
    pub(crate) fn implies(self, clause: ClauseFSet) -> bool {
        pearlite! {
            self.eventually_sat_complete() ==> self.insert(clause).eventually_sat_complete()
        }
    }

    #[predicate]
    pub(crate) fn eventually_sat_complete(self) -> bool {
        pearlite! {
            exists<a: AssignmentsModel> a.0.len() == self.num_vars
            && a.invariant()
            && a.complete()
            && self.sat(a)
        }
    }

    #[predicate]
    pub(crate) fn sat(self, a: AssignmentsModel) -> bool {
        pearlite! {
            forall<c: _> self.formula.contains(c) ==> c.sat(a)
        }
    }
}
