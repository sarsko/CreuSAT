extern crate creusot_contracts;

use creusot_contracts::{std::clone::Clone, std::*, vec, *};

use crate::{assignments::*, clause_allocator::*, cref_manager::*, lit::*};

use crate::{clause::*, formula::*, logic_util::*};
#[cfg(creusot)]
use crate::cref::cref_invariant;

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
    #[requires(self.original_clauses().implies(clause.to_fset()))]
    #[ensures(result.0.invariant())]
    //#[ensures(result.0.original_clauses() == self.original_clauses())]
    //#[ensures(self.original_clauses == result.0.original_clauses)]
    #[ensures(self.original_clauses.crefs.ext_eq(result.0.original_clauses.crefs))]
    #[ensures(forall<i: Int> 0 <= i && i < self.clause_allocator.buffer.len() ==> 
        self.clause_allocator.buffer[i] == result.0.clause_allocator.buffer[i])]
    #[ensures(cref_invariant(result.1, result.0.clause_allocator, result.0.clause_allocator.num_vars))]
    #[ensures(forall<i: Int> 0 <= i && i < self.original_clauses.crefs.len() ==>
        0 <= self.original_clauses.crefs[i] && self.original_clauses.crefs[i] < self.clause_allocator.buffer.len())]
    #[ensures(forall<c: _> result.0.original_clauses().formula.contains(c) ==> self.original_clauses().formula.contains(c))]
    #[ensures(forall<c: _> self.original_clauses().formula.contains(c) ==> result.0.original_clauses().formula.contains(c))]
    pub(crate) fn learn_clause(self, clause: ClauseSeq) -> (Self, Int) {
        let (new_clause_allocator, cref) = self.clause_allocator.add_clause(clause, self.original_clauses, self.learnt_core);
        if self.original_clauses().implies(new_clause_allocator.get_clause_fset(cref)) {}
        //let new_learnt_core = self.learnt_core.push(cref, new_clause_allocator);
        let new_learnt_core = self.learnt_core.push2(cref, new_clause_allocator, self.original_clauses);
        let result = (
            Self {
                clause_allocator: new_clause_allocator,
                original_clauses: self.original_clauses,
                learnt_core: new_learnt_core,
            },
            cref,
        );

        if self.original_clauses.crefs.ext_eq(result.0.original_clauses.crefs) {}
        if result.0.invariant() {}
        lemma_original_clauses_maintained(self, result.0);

        result
    }

    #[logic]
    #[requires(self.invariant())]
    #[ensures(result.num_vars == self.clause_allocator.num_vars)]
    #[ensures(forall<i: Int> 0 <= i && i < self.original_clauses.crefs.len() ==> exists<c: _> result.formula.contains(c) 
        && self.clause_allocator.get_clause_fset(self.original_clauses.crefs[i]) == c)]
    #[ensures(forall<c: _> result.formula.contains(c) ==> 
        exists<i: Int> 0 <= i && i < self.original_clauses.crefs.len() && self.clause_allocator.get_clause_fset(self.original_clauses.crefs[i]) == c)]
    pub(crate) fn original_clauses(self) -> Formula {
        Formula::from(self.original_clauses.crefs, self.clause_allocator, self.clause_allocator.num_vars)
    }
}


#[logic]
#[requires(cm1.original_clauses == cm2.original_clauses)]
#[requires(cm1.clause_allocator.extended(cm2.clause_allocator))]
#[requires(cm1.invariant())]
#[requires(cm2.invariant())]
#[ensures(forall<i: _> 0 <= i && i < cm1.original_clauses.crefs.len()
     ==> cm1.clause_allocator.get_clause_seq(cm1.original_clauses.crefs[i]) == cm2.clause_allocator.get_clause_seq(cm1.original_clauses.crefs[i]))]
#[ensures(forall<i: _> 0 <= i && i < cm1.original_clauses.crefs.len()
     ==> cm1.clause_allocator.get_clause_fset(cm1.original_clauses.crefs[i]) == cm2.clause_allocator.get_clause_fset(cm1.original_clauses.crefs[i]))]
#[ensures(forall<c: _> cm1.original_clauses().formula.contains(c) ==> cm2.original_clauses().formula.contains(c))]
#[ensures(forall<c: _> cm2.original_clauses().formula.contains(c) ==> cm1.original_clauses().formula.contains(c))]
fn lemma_original_clauses_maintained(cm1: ClauseManagerModel, cm2: ClauseManagerModel) {
    lemma_ext_eq_to_eq(cm1, cm2)
}

#[logic]
#[requires(forall<i: _> 0 <= i && i < cm1.original_clauses.crefs.len()
    ==> cm1.clause_allocator.get_clause_seq(cm1.original_clauses.crefs[i]).lits.ext_eq(cm2.clause_allocator.get_clause_seq(cm1.original_clauses.crefs[i]).lits))]
#[ensures(forall<i: _> 0 <= i && i < cm1.original_clauses.crefs.len()
     ==> cm1.clause_allocator.get_clause_seq(cm1.original_clauses.crefs[i]) == cm2.clause_allocator.get_clause_seq(cm1.original_clauses.crefs[i]))]
fn lemma_ext_eq_to_eq(cm1: ClauseManagerModel, cm2: ClauseManagerModel) {}

#[logic]
#[requires(cref_invariant(cref, ca1, ca1.num_vars))]
#[requires(cref_invariant(cref, ca2, ca2.num_vars))]
#[requires(ca1.extended(ca2))]
#[requires(ca1.invariant())]
#[requires(ca2.invariant())]
#[ensures(ca1.get_clause_seq(cref) == ca2.get_clause_seq(cref))]
fn lemma_cref_eq_seq(cref: Int, ca1: ClauseAllocatorModel, ca2: ClauseAllocatorModel) {
    if ca1.get_clause_seq(cref).lits.ext_eq(ca2.get_clause_seq(cref).lits) {}
}


#[logic]
#[requires(cref_invariant(cref, ca1, ca1.num_vars))]
#[requires(cref_invariant(cref, ca2, ca2.num_vars))]
#[requires(ca1.extended(ca2))]
#[requires(ca1.invariant())]
#[requires(ca2.invariant())]
#[requires(ca1.buffer[cref] == ca2.buffer[cref])]
#[ensures(ca1.get_clause_fset(cref).lits.ext_eq(ca2.get_clause_fset(cref).lits))]
//#[ensures(ca1.get_clause_seq(cref).lits.ext_eq(ca2.get_clause_seq(cref).lits))]
//#[ensures(ca1.get_clause_fset(cref) == ca2.get_clause_fset(cref))]
fn lemma_cref_ext_eq_fset(cref: Int, ca1: ClauseAllocatorModel, ca2: ClauseAllocatorModel) {
    //#[ensures(ca1.get_clause_seq(cref).lits.ext_eq(ca2.get_clause_seq(cref).lits))]
    //if ca1.get_clause_(cref).lits.ext_eq(ca2.get_clause_seq(cref).lits) {}
}

#[logic]
#[requires(ca1.get_clause_fset(cref).lits.ext_eq(ca2.get_clause_fset(cref).lits))]
#[ensures(ca1.get_clause_fset(cref) == ca2.get_clause_fset(cref))]
fn lemma_cref_eq_fset(cref: Int, ca1: ClauseAllocatorModel, ca2: ClauseAllocatorModel) {}

#[requires(cref_invariant(cref, ca1, ca1.num_vars))]
#[requires(cref_invariant(cref, ca2, ca2.num_vars))]
#[requires(ca1.invariant())]
#[requires(ca2.invariant())]
#[requires(ca1.extended(ca2))]
#[requires(ca1.get_clause_seq(cref) == ca2.get_clause_seq(cref))]
#[ensures(ca1.get_clause_fset(cref) == ca2.get_clause_fset(cref))]
fn lemma_cref_seq_to_fset(cref: Int, ca1: ClauseAllocatorModel, ca2: ClauseAllocatorModel) {}
