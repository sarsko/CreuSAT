extern crate creusot_contracts;

use creusot_contracts::logic::FSet;
use creusot_contracts::{std::clone::Clone, std::*, vec, *};

use crate::cref_manager::CRefManagerModel;
use crate::{clause::*, lit::*};

use crate::logic_util::*;

// TODO: Decide on whether to have it as a type or a struct
//pub type CRef = u32;

// TODO: This seems to be a non-ideal invariant
// TODO: Add more
#[predicate]
pub(crate) fn cref_invariant(cref: Int, clause_allocator: ClauseAllocatorModel, num_vars: Int) -> bool {
    pearlite! {
        0 <= cref && cref < clause_allocator.buffer.len()
        && clause_allocator.buffer[cref].code + cref + HEADER_LEN@ <= clause_allocator.buffer.len() // TODO: Do I need this?
        //&& clause_allocator.get_clause_seq(cref).invariant(num_vars)
        //clause_allocator.buffer.subsequence(cref + HEADER_LEN@, cref + HEADER_LEN@ + self.buffer[cref].code)
    }
}

#[predicate]
pub(crate) fn cref_invariant_fset(cref: Int, clause_allocator: ClauseAllocatorModel, num_vars: Int) -> bool {
    pearlite! {
        cref < clause_allocator.buffer.len()
        && clause_allocator.buffer[cref].code + cref + HEADER_LEN@ <= clause_allocator.buffer.len() // TODO: Do I need this?
        && clause_allocator.get_clause_fset(cref).invariant(num_vars)
    }
}

/*
// TODO: unpub buffer
pub(crate) struct ClauseAllocator {
    pub(crate) buffer: Vec<Lit>,
    pub(crate) num_vars: usize, // TODO: Look for a way to not have to store this everywhere
}

#[cfg(creusot)]
impl ShallowModel for ClauseAllocator {
    type ShallowModelTy = ClauseAllocatorModel;

    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        ClauseAllocatorModel { buffer: self.buffer.shallow_model(), num_vars: self.num_vars.shallow_model() }
    }
}
*/

pub const HEADER_LEN: usize = 2;

/*
impl ClauseAllocator {
    // TODO: This is struggling with no_duplicate_indexes and FSet/Seq stuff
    // TODO: Maintains is broken by "new scheme"
    // Hmm, this is a poor example for the model scheme
    #[requires(self@.invariant())]
    #[requires(lits@.len() > 0)]
    #[requires(ClauseSeq{ lits: lits@ }.invariant(self.num_vars@))]
    #[requires(self@.buffer.len() + lits@.len() + HEADER_LEN@ <= u32::MAX@)] // TODO: May have to move this to a runtime check

    //#[ensures((^self)@ == self@.add_clause(ClauseSeq{ lits: lits@} ).0)]
    //#[ensures(result@  == self@.add_clause(ClauseSeq{ lits: lits@} ).1)]

    //#[ensures((^self)@.invariant())]
    //#[ensures((^self).num_vars == self.num_vars)]
    //#[ensures((^self)@.buffer.len() == self@.buffer.len() + lits@.len() + HEADER_LEN@)]
    //#[ensures(cref_invariant(result@, (^self)@, self.num_vars@))]
    //#[ensures(result@ == self@.buffer.len())]
    //#[ensures((^self)@.buffer[result@].code@ == lits@.len())]
    //#[ensures(forall<i: Int> 0 <= i && i < self@.buffer.len() ==> (^self)@.buffer[i] == self@.buffer[i])] // Head unchanged. TODO: Refactor ?
    //#[ensures(forall<i: Int> 0 <= i && i < lits@.len() ==> (^self)@.buffer[result@ + HEADER_LEN@ + i] == lits@[i])] // Extended. TODO: Refactor ?
    pub(crate) fn add_clause(&mut self, lits: &[Lit]) -> CRef {
        let cref = self.buffer.len() as CRef;
        self.buffer.push(Lit::raw(lits.len() as u32));

        let old_self: Ghost<&mut ClauseAllocator> = ghost!(self);

        #[invariant(self.num_vars == old_self.num_vars)] // TODO: Don't like this
        #[invariant(^*old_self == ^self)]
        #[invariant(self@.buffer.len() == old_self@.buffer.len() + produced.len())]
        #[invariant(forall<i: Int> 0 <= i && i < old_self@.buffer.len() ==> self@.buffer[i] == old_self@.buffer[i])] // TODO: Refactor ?
        #[invariant(forall<i: Int> 0 <= i && i < self@.buffer.len() - old_self@.buffer.len() ==>
                    self@.buffer[cref@ + HEADER_LEN@ + i] == lits@[i])]
        #[invariant(forall<i: Int> 0 <= i && i < self@.buffer.len() - old_self@.buffer.len() ==>
                    self@.buffer[cref@ + HEADER_LEN@ + i]@.var_in_range(self.num_vars@))]
        //#[invariant(forall<i: Int> 0 <= i && i < (produced).len() ==> self@[cref@ + HEADER_LEN@ + i] == *(produced)[i])]
        //#[invariant(forall<i: Int> 0 <= i && i < (produced).len() ==> self@[cref@ + HEADER_LEN@ + i] == (@lits)[i]
        //            && self@[cref@ + HEADER_LEN@ + i].var_in_range(self.num_vars@))]
        for lit in lits {
            self.buffer.push(*lit);
        }

        cref
    }

    #[requires(self@.invariant())]
    #[requires(cref_invariant(cref@, self@, self.num_vars@))]
    #[ensures(result@ == self@.get_clause_seq(cref@).lits)] // TODO: Correct way to do this? Rather create a ClauseSeq from the result?
    pub(crate) fn get_clause(&self, cref: u32) -> &[Lit] {
        let idx = cref as usize;
        let len = self.buffer[idx].code as usize;
        &self.buffer[idx + HEADER_LEN..idx + HEADER_LEN + len]
    }
}
*/

pub struct ClauseAllocatorModel {
    pub(crate) buffer: Seq<LitModel>,
    pub(crate) num_vars: Int, // TODO: Look for a way to not have to store this everywhere
}

impl ClauseAllocatorModel {
    #[predicate]
    pub(crate) fn invariant(self) -> bool {
        true
    }
    /*
    #[predicate]
    pub(crate) fn invariant(self) -> bool {
        pearlite! { self.buffer.len() <= u32::MAX@ }
    }
    */

    #[predicate]
    //#[requires(self.invariant())]
    //#[requires(new.invariant())]
    pub(crate) fn extended(self, new: ClauseAllocatorModel) -> bool {
        pearlite! {
            self.num_vars == new.num_vars
            && self.buffer.len() < new.buffer.len()
            //&& self.buffer@ == new.buffer@.subsequence(0, self.buffer@.len())
            && forall<i: Int> 0 <= i && i < self.buffer.len() ==> self.buffer[i] == new.buffer[i]
        }
    }
}

impl ClauseAllocatorModel {
    #[logic]
    //#[requires(cref_invariant(cref, self))]
    pub(crate) fn get_clause_seq(self, cref: Int) -> ClauseSeq {
        pearlite! {
            ClauseSeq { lits: self.buffer.subsequence(cref + HEADER_LEN@, cref + HEADER_LEN@ + self.buffer[cref].code) }
        }
    }

    #[logic]
    //#[requires(cref_invariant(cref, self))]
    pub(crate) fn get_clause_fset(self, cref: Int) -> ClauseFSet {
        pearlite! {
            ClauseFSet { lits: self.get_clause_fset_internal(cref, cref + HEADER_LEN@, cref + HEADER_LEN@ + self.buffer[cref].code) }
        }
    }

    #[logic]
    //#[requires(cref_invariant(cref, self))]
    #[variant(upper - idx)]
    #[requires(idx >= 0 && upper <= self.buffer.len())]
    fn get_clause_fset_internal(self, cref: Int, idx: Int, upper: Int) -> FSet<LitModel> {
        pearlite! {
            if idx < upper {
                let set = self.get_clause_fset_internal(cref, idx + 1, upper);
                set.insert(self.buffer[cref + idx])
            } else {
                FSet::EMPTY
            }
        }
    }

    // TODO: Increase header size and store header as well.
    // NOTE: If the ClauseManagers are passed then things pass quicker
    #[logic]
    #[requires(self.invariant())]
    #[requires(clause.lits.len() > 0)]
    #[requires(clause.invariant(self.num_vars))]
    #[ensures(self.extended(result.0))]
    #[ensures(cref_invariant(result.1, result.0, result.0.num_vars))]
    #[ensures(result.0.invariant())]
    #[ensures(forall<i: Int> 0 <= i && i < self.buffer.len() ==> self.buffer[i] == result.0.buffer[i])]
    pub(crate) fn add_clause(self, clause: ClauseSeq) -> (Self, Int) {
        let cref = self.buffer.len();
        let tmp_buffer = self.buffer.push(LitModel { code: clause.lits.len() });

        let header = clause.calc_header();
        let tmp_buffer = tmp_buffer.push(LitModel { code: header });

        (Self { buffer: tmp_buffer.concat(clause.lits), num_vars: self.num_vars }, cref)
    }
}
