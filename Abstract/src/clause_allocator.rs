extern crate creusot_contracts;

use creusot_contracts::logic::FSet;
use creusot_contracts::{std::clone::Clone, std::*, vec, *};

use crate::cref_manager::CRefManagerModel;
use crate::{clause::*, lit::*};

use crate::logic_util::*;
use crate::cref::cref_invariant;


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
        pearlite! {
            forall<i: Int> 0 <= i && i < self.buffer.len() ==> self.buffer[i].invariant()
        }
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
            //&& self.buffer == new.buffer.subsequence(0, self.buffer.len())
            && forall<i: Int> 0 <= i && i < self.buffer.len() ==> self.buffer[i] == new.buffer[i]
        }
    }
}

impl ClauseAllocatorModel {
    // TODO: Add circularity ensures for this and fset ?
    #[logic]
    // TODO: Cref invariant partially unfolded (perhaps split it up to avoid the circularity)
    #[requires(
        0 <= cref && cref < self.buffer.len()
        && self.buffer[cref].code + cref + HEADER_LEN@ <= self.buffer.len()
    )]
    #[requires(self.invariant())]
    #[ensures(result.lits == self.buffer.subsequence(cref + HEADER_LEN@, cref + HEADER_LEN@ + self.buffer[cref].code))]
    #[ensures(result.lits.len() == self.buffer[cref].code)]
    pub(crate) fn get_clause_seq(self, cref: Int) -> ClauseSeq {
        pearlite! {
            ClauseSeq { lits: self.buffer.subsequence(cref + HEADER_LEN@, cref + HEADER_LEN@ + self.buffer[cref].code) }
        }
    }

    // TODO: Add circularity ensures for this and seq ?
    #[logic]
    // TODO: Cref invariant partially unfolded (perhaps split it up to avoid the circularity)
    #[requires(
        0 <= cref && cref < self.buffer.len()
        && self.buffer[cref].code + cref + HEADER_LEN@ <= self.buffer.len()
    )]
    #[requires(self.invariant())]
    #[ensures(result.lits.len() <= self.buffer[cref].code)] // Change this to eq by adding a no-duplicate bound on clauses?
    #[ensures(result.lits == self.get_clause_seq(cref).lits.to_set())]
    pub(crate) fn get_clause_fset(self, cref: Int) -> ClauseFSet {
        pearlite! {
            //ClauseFSet { lits: self.get_clause_fset_internal(cref, cref + HEADER_LEN@, cref + HEADER_LEN@ + self.buffer[cref].code) }
            ClauseFSet { lits: self.buffer.subsequence(cref + HEADER_LEN@, cref + HEADER_LEN@ + self.buffer[cref].code).to_set() }
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
    #[requires(oc.invariant(self))]
    #[requires(lc.invariant(self))]
    #[ensures(self.extended(result.0))]
    #[ensures(cref_invariant(result.1, result.0, result.0.num_vars))]
    #[ensures(result.0.invariant())]
    #[ensures(forall<i: Int> 0 <= i && i < self.buffer.len() ==> self.buffer[i] == result.0.buffer[i])]
    #[ensures(result.0.get_clause_seq(result.1) == clause)]
    //#[ensures(result.0.get_clause_seq(result.1).is_m)]
    #[ensures(oc.invariant(result.0))]
    #[ensures(lc.invariant(result.0))]
    pub(crate) fn add_clause(self, clause: ClauseSeq, oc: CRefManagerModel, lc: CRefManagerModel) -> (Self, Int) {
        let cref = self.buffer.len();
        //let tmp_buffer = self.buffer.push(LitModel { code: clause.lits.len() });
        let tmp_buffer = self.buffer.push(LitModel { code: clause.len() });

        let header = clause.calc_header();
        let tmp_buffer2 = tmp_buffer.push(LitModel { code: header });

        let result = (Self { buffer: tmp_buffer2.concat(clause.lits), num_vars: self.num_vars }, cref);

        // Trick to get the SMT solvers to apply ext_eq so that we get ==
        if clause.lits.ext_eq(result.0.get_clause_seq(result.1).lits) {}

        result
    }
}
