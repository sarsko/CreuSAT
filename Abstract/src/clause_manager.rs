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
    /*
    #[logic]
    pub(crate) fn learn_clause(self) -> CRef {
    }
    */

    #[logic]
    #[requires(self.invariant())]
    pub(crate) fn original_clauses(self) -> Formula {
        Formula::from(self.original_clauses.crefs, self.clause_allocator, self.clause_allocator.num_vars)
    }
}

/*
#[logic]
#[requires(learnt_clauses.are_implied_by(original_clauses, ca))]
#[ensures(learnt_clauses.are_implied_by(original_clauses, ca.push(lit)))]
fn lemma_implied_by_stable_on_push(
    original_clauses: CRefManager, learnt_clauses: CRefManager, ca: ClauseAllocator, lit: Lit,
) {
}

/*
#[logic]
#[requires(learnt_clauses.are_implied_by(original_clauses, ca))]
#[requires(ca.extended(ca2))]
#[requires(ca2
//#[requires(ca2.extended(ca))]
#[ensures(learnt_clauses.are_implied_by(original_clauses, ca2))]
fn lemma_implied_by_stable_on_extension(
    original_clauses: CRefManager, learnt_clauses: CRefManager, ca: ClauseAllocator, ca2: ClauseAllocator, lit: Lit,
) {}
*/

#[logic]
#[requires(learnt_clauses.are_implied_by(original_clauses, ca))]
#[requires(ca.extended(ca2))]
//#[requires(ca2.extended(ca))]
#[ensures(learnt_clauses.are_implied_by(original_clauses, ca2))]
fn lemma_implied_by_stable_on_extension(
    original_clauses: CRefManager, learnt_clauses: CRefManager, ca: ClauseAllocator, ca2: ClauseAllocator,
) {}

#[logic]
#[requires(learnt_clauses.are_implied_by(original_clauses, ca))]
#[requires(ca.extended(ca2))]
#[requires(ca2.extended(ca))]
#[ensures(ca == ca2)]
fn lemma_extended_means_eq(
    original_clauses: CRefManager, learnt_clauses: CRefManager, ca: ClauseAllocator, ca2: ClauseAllocator,
) {}

#[logic]
#[requires(learnt_clauses.are_implied_by(original_clauses, ca))]
#[requires(ca.extended(ca2))]
#[requires(ca2.extended(ca))]
#[ensures(ca@.len() == ca2@.len())]
fn lemma_extended_means_eq_len(
    original_clauses: CRefManager, learnt_clauses: CRefManager, ca: ClauseAllocator, ca2: ClauseAllocator,
) {}

#[logic]
#[requires(learnt_clauses.are_implied_by(original_clauses, ca))]
#[requires(ca.extended(ca2))]
#[requires(ca2.extended(ca))]
#[ensures(ca.buffer@ == ca2.buffer@)]
fn lemma_extended_means_eq_buffer(
    original_clauses: CRefManager, learnt_clauses: CRefManager, ca: ClauseAllocator, ca2: ClauseAllocator,
) {}

#[logic]
#[requires(learnt_clauses.are_implied_by(original_clauses, ca))]
#[requires(ca.buffer@.len() > 0)]
#[requires(ca2@ == ca@.subsequence(0, ca.buffer@.len()))]
#[requires(ca@ == ca2@.subsequence(0, ca.buffer@.len()))]
#[requires(ca2.buffer@.len() == ca.buffer@.len())]
#[ensures(ca.buffer@ == ca2.buffer@)]
fn lemma_subseq(
    original_clauses: CRefManager, learnt_clauses: CRefManager, ca: ClauseAllocator, ca2: ClauseAllocator,
) {}

#[logic]
#[requires(learnt_clauses.are_implied_by(original_clauses, ca))]
#[requires(ca.num_vars == ca2.num_vars)]
#[requires(forall<i: Int> 0 <= i && i < ca.buffer@.len() ==> ca@[i] == ca2@[i])]
#[requires(forall<i: Int> 0 <= i && i < ca2.buffer@.len() ==> ca@[i] == ca2@[i])]
#[requires(ca2.buffer@.len() == ca.buffer@.len())]
#[ensures(learnt_clauses.are_implied_by(original_clauses, ca2))]
fn lemma_implied_by_stable_on_blim(
    original_clauses: CRefManager, learnt_clauses: CRefManager, ca: ClauseAllocator, ca2: ClauseAllocator,
) {
}


*/
