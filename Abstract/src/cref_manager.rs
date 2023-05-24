extern crate creusot_contracts;

use creusot_contracts::{std::clone::Clone, std::*, vec, *};

use crate::{
    assignments::*,
    clause_allocator::{self, *},
    lit::*,
};

use crate::formula::*;
use crate::cref::cref_invariant;

/*
pub struct CRefManager {
    crefs: Vec<CRef>,
    pub(crate) num_vars: usize,
}
*/

/*
#[cfg(creusot)]
impl ShallowModel for CRefManager {
    type ShallowModelTy = CRefManagerModel;

    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        CRefManagerModel { crefs: self.crefs.shallow_model(), num_vars: self.num_vars.shallow_model() }
    }
}

impl CRefManager {
    // TODO: Passing the clause allocator is super ugly and I should refactor
    // TODO: maintains is broken by "new" scheme
    #[requires(self@.invariant(_clause_allocator@))]
    #[requires(cref_invariant(cref@, _clause_allocator@, self.num_vars@))]
    //#[ensures((^self)@.invariant(_clause_allocator@))] // Get this from push
    #[ensures((^self)@ == self@.push(cref, _clause_allocator@))]
    //#[ensures(forall<i: Int> 0 <= i && i < self@.crefs.len() ==> self@.crefs[i] == (^self)@.crefs[i])] // Get this from push as well.
    //#[ensures((^self)@.crefs[self@.crefs.len()] == cref)] // TODO: Refactor to (^self).last() == cref ? // No, just get it from push
    pub(crate) fn add_cref(&mut self, cref: CRef, _clause_allocator: &ClauseAllocator) {
        self.crefs.push(cref);
    }
}
*/


// TODO: Impl Index?
pub struct CRefManagerModel {
    pub(crate) crefs: Seq<Int>,
    pub(crate) num_vars: Int,
}

impl CRefManagerModel {
    #[predicate]
    pub(crate) fn invariant(self, clause_allocator: ClauseAllocatorModel) -> bool {
        pearlite! {
            clause_allocator.invariant()
            && self.num_vars == clause_allocator.num_vars && // TODO: Fix the double storing
            forall<i: Int> 0 <= i && i < self.crefs.len() ==>
                cref_invariant(self.crefs[i], clause_allocator, clause_allocator.num_vars)
        }
    }

    #[predicate]
    pub(crate) fn are_implied_by(
        self, original_clauses: CRefManagerModel, clause_allocator: ClauseAllocatorModel,
    ) -> bool {
        pearlite! {
            let formula = Formula::from(original_clauses.crefs, clause_allocator, self.num_vars);
            forall<i: Int> 0 <= i && i < self.crefs.len() ==>
                    formula.implies(clause_allocator.get_clause_fset(self.crefs[i]))
        }
    }
}

impl CRefManagerModel {
    #[logic]
    #[requires(self.invariant(clause_allocator))]
    #[requires(cref_invariant(cref, clause_allocator, clause_allocator.num_vars))]
    #[ensures(result.invariant(clause_allocator))]
    // TODO: unsure whether these are needed
    #[ensures(result.crefs == self.crefs.push(cref))]
    #[ensures(result.num_vars == self.num_vars)]
    pub(crate) fn push(self, cref: Int, clause_allocator: ClauseAllocatorModel) -> Self {
        Self { crefs: self.crefs.push(cref), num_vars: self.num_vars }
    }

    #[logic]
    #[requires(self.invariant(clause_allocator))]
    #[requires(cref_invariant(cref, clause_allocator, clause_allocator.num_vars))]
    #[requires(
        Formula::from(orig.crefs, clause_allocator, clause_allocator.num_vars)
        .implies(clause_allocator.get_clause_fset(cref)))]
    #[ensures(result.invariant(clause_allocator))]

    #[ensures(result.are_implied_by(orig, clause_allocator))]
    // TODO: unsure whether these are needed
    #[ensures(result.crefs == self.crefs.push(cref))]
    #[ensures(result.num_vars == self.num_vars)]
    pub(crate) fn push2(self, cref: Int, clause_allocator: ClauseAllocatorModel, orig: CRefManagerModel) -> Self {
        Self { crefs: self.crefs.push(cref), num_vars: self.num_vars }
    }
}
