extern crate creusot_contracts;

use creusot_contracts::{std::clone::Clone, std::*, vec, *};

use crate::{assignments::*, clause_allocator::*, cref_manager::*, lit::*};

use crate::{clause::*, formula::*, logic_util::*};

/*
pub struct ClauseManager {
    clause_allocator: ClauseAllocator,
    original_clauses: CRefManager,
    learnt_core: CRefManager,
}

#[cfg(creusot)]
impl ShallowModel for ClauseManager {
    type ShallowModelTy = ClauseManagerModel;

    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        ClauseManagerModel {
            clause_allocator: self.clause_allocator.shallow_model(),
            original_clauses: self.original_clauses.shallow_model(),
            learnt_core: self.learnt_core.shallow_model(),
        }
    }
}

// Going to need two lemmas here it seems: one for adding a clause without binding it cannot change
// anything, and one for binding a clause which is implied maintains the invariant.
impl ClauseManager {
    // TODO: Maintains broken by "new scheme"
    #[requires(self@.invariant())]
    #[requires(lits@.len() > 0)]
    #[requires(self@.clause_allocator.buffer.len() + lits@.len() + HEADER_LEN@ <= u32::MAX@)] // TODO: May have to move this to a runtime check
    #[requires(ClauseSeq { lits: lits@ }.invariant(self.clause_allocator.num_vars@))]
    //#[ensures((^self)@.invariant())]
    //#[requires(Formula::from(self@.original_clauses.crefs, self@.clause_allocator, self@.clause_allocator.num_vars).implies(ClauseFSet { lits: seq_to_fset(lits@) }))]
    #[requires(self@.original_clauses().implies(ClauseFSet { lits: seq_to_fset(lits@) }))]
    // TODO: Not get crefs from original_clauses?
    //#[requires(self@.len() + (@lits).len() + @HEADER_LEN <= @u32::MAX)] // TODO: May have to move this to a runtime check
    pub(crate) fn learn_clause(&mut self, lits: &[Lit]) -> CRef {
        //let old_self: Ghost<&mut ClauseManager> = ghost!(self);
        //proof_assert!(self@.learnt_core.are_implied_by(self@.original_clauses, self@.clause_allocator));
        let cref = self.clause_allocator.add_clause(lits);
        //proof_assert!(^*old_self == ^self);
        let ca = &self.clause_allocator;
        //proof_assert!(self@.learnt_core.are_implied_by(self@.original_clauses, self@.clause_allocator));
        self.learnt_core.add_cref(cref, &ca);
        //proof_assert!(self.learnt_core.are_implied_by(self.original_clauses, self.clause_allocator));
        cref
    }
}
*/

pub struct ClauseManagerModel {
    clause_allocator: ClauseAllocatorModel,
    original_clauses: CRefManagerModel,
    learnt_core: CRefManagerModel,
}

impl ClauseManagerModel {
    #[predicate]
    pub(crate) fn invariant(self) -> bool {
        pearlite! {
            self.clause_allocator.invariant()
            && self.original_clauses.invariant(self.clause_allocator)
            && self.learnt_core.invariant(self.clause_allocator)
            && self.learnt_core.are_implied_by(self.original_clauses, self.clause_allocator)
        }
    }
}

impl ClauseManagerModel {
    #[logic]
    #[requires(self.invariant())]
    #[requires(clause.lits.len() > 0)]
    #[requires(clause.invariant(self.clause_allocator.num_vars))]
    #[ensures(result.0.invariant())]
    #[ensures(cref_invariant(result.1, result.0.clause_allocator, result.0.clause_allocator.num_vars))]
    pub(crate) fn learn_clause(self, clause: ClauseSeq) -> (Self, Int) {
        let (new_clause_allocator, cref) = self.clause_allocator.add_clause(clause);
        let new_learnt_core = self.learnt_core.push(cref, new_clause_allocator);
        (
            Self {
                clause_allocator: new_clause_allocator,
                original_clauses: self.original_clauses,
                learnt_core: new_learnt_core,
            },
            cref,
        )
    }

    #[logic]
    #[requires(self.invariant())]
    pub(crate) fn original_clauses(self) -> Formula {
        Formula::from(self.original_clauses.crefs, self.clause_allocator, self.clause_allocator.num_vars)
    }
}

