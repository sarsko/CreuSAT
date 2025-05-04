

use creusot_contracts::{std::clone::Clone, std::*, vec, *};

use crate::{assignments::*, clause_allocator::*, cref_manager::*, lit::*};

use crate::{clause::*, formula::*, logic_util::*};

pub struct ClauseManager {
    clause_allocator: ClauseAllocator,
    original_clauses: CRefManager,
    learnt_core: CRefManager,
}

impl ClauseManager {
    #[open]
    #[predicate]
    pub(crate) fn inv(self) -> bool {
        pearlite! {
            self.clause_allocator.inv()
            && self.original_clauses.inv(self.clause_allocator)
            && self.learnt_core.inv(self.clause_allocator)
            && self.learnt_core.are_implied_by(self.original_clauses, self.clause_allocator)
        }
    }
}

#[open]
#[logic]
#[requires(learnt_clauses.are_implied_by(original_clauses, ca))]
#[ensures(learnt_clauses.are_implied_by(original_clauses, ca.push(lit)))]
fn lemma_implied_by_stable_on_push(
    original_clauses: CRefManager, learnt_clauses: CRefManager, ca: ClauseAllocator, lit: Lit,
) {
}

#[open]
#[logic]
#[requires(learnt_clauses.are_implied_by(original_clauses, ca))]
#[requires(ca.extended(ca2))]
#[requires(ca2.extended(ca))]
#[ensures(learnt_clauses.are_implied_by(original_clauses, ca2))]
fn lemma_implied_by_stable_on_extension(
    original_clauses: CRefManager, learnt_clauses: CRefManager, ca: ClauseAllocator, ca2: ClauseAllocator,
) {
}

#[open]
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

// Going to need two lemmas here it seems: one for adding a clause without binding it cannot change
// anything, and one for binding a clause which is implied maintains the invariant.
impl ClauseManager {
    #[maintains((mut self).inv())]
    #[requires(lits@.len() > 0)]
    #[requires(self.clause_allocator@.len() + lits@.len() + HEADER_LEN@ <= u32::MAX@)] // TODO: May have to move this to a runtime check
    #[requires(Formula::from(self.original_clauses@, self.clause_allocator, self.clause_allocator.num_vars@).implies(seq_to_fset(lits@)))]
    //#[requires(self@.len() + (@lits).len() + @HEADER_LEN <= @u32::MAX)] // TODO: May have to move this to a runtime check
    #[requires(clause_invariant_seq(lits@, self.clause_allocator.num_vars@))]
    pub(crate) fn learn_clause(&mut self, lits: &[Lit]) -> CRef {
        let old_self: Snapshot<&mut ClauseManager> = snapshot!(self);
        proof_assert!(self.learnt_core.are_implied_by(self.original_clauses, self.clause_allocator));
        let cref = self.clause_allocator.add_clause(lits);
        proof_assert!(^*old_self == ^self);
        let ca = &self.clause_allocator;
        proof_assert!(self.learnt_core.are_implied_by(self.original_clauses, self.clause_allocator));
        self.learnt_core.add_cref(cref, &ca);
        //proof_assert!(self.learnt_core.are_implied_by(self.original_clauses, self.clause_allocator));
        cref
    }
}
