extern crate creusot_contracts;

use creusot_contracts::{std::clone::Clone, std::*, vec, *};

use crate::{assignments::*, clause_allocator::*, lit::*};

use crate::formula::*;

pub struct CRefManager {
    crefs: Vec<CRef>,
    pub(crate) num_vars: usize,
}

#[cfg(creusot)]
impl ShallowModel for CRefManager {
    type ShallowModelTy = Seq<CRef>;

    #[open]
#[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.crefs.shallow_model()
    }
}

impl CRefManager {
    #[open]
#[predicate]
    pub(crate) fn invariant(self, clause_allocator: ClauseAllocator) -> bool {
        pearlite! {
            clause_allocator.invariant()
            && self.num_vars@ == clause_allocator.num_vars@ && // TODO: Fix the double storing
            forall<i: Int> 0 <= i && i < self@.len() ==>
                cref_invariant(self@[i]@, clause_allocator, clause_allocator.num_vars@)
        }
    }

    #[open]
#[predicate]
    pub(crate) fn are_implied_by(self, original_clauses: CRefManager, clause_allocator: ClauseAllocator) -> bool {
        pearlite! {
            let formula = Formula::from(self@, clause_allocator, self.num_vars@);
            forall<i: Int> 0 <= i && i < self@.len() ==>
                    formula.implies(clause_allocator.get_clause_fset(self@[i]@))
        }
    }
}

impl CRefManager {
    // TODO: Passing the clause allocator is super ugly and I should refactor
    #[maintains((mut self).invariant(*_clause_allocator))]
    #[requires(cref_invariant(cref@, *_clause_allocator, self.num_vars@))]
    #[ensures((^self)@ == self@.push(cref))]
    #[ensures(forall<i: Int> 0 <= i && i < self@.len() ==> self@[i] == (^self)@[i])]
    #[ensures((^self)@[self@.len()] == cref)]
    pub(crate) fn add_cref(&mut self, cref: CRef, _clause_allocator: &ClauseAllocator) {
        self.crefs.push(cref);
    }
}
