use creusot_contracts::logic::FSet;
use creusot_contracts::{std::clone::Clone, std::*, vec, *};

use crate::{clause::*, lit::*};

use crate::logic_util::*;

// TODO: Decide on whether to have it as a type or a struct
pub type CRef = u32;

// TODO: This seems to be a non-ideal invariant
// TODO: Add more
#[open]
#[predicate]
pub(crate) fn cref_invariant(cref: Int, clause_allocator: ClauseAllocator, num_vars: Int) -> bool {
    pearlite! {
        cref < clause_allocator@.len()
        && clause_allocator@[cref].code@ + cref + HEADER_LEN@ <= clause_allocator@.len()
        //&& clause_invariant(clause_allocator.get_clause_fset(cref), num_vars)
        && clause_invariant_seq(clause_allocator.get_clause_logic(cref), num_vars)
    }
}

#[open]
#[predicate]
pub(crate) fn cref_invariant_fset(cref: Int, clause_allocator: ClauseAllocator, num_vars: Int) -> bool {
    pearlite! {
        cref < clause_allocator@.len()
        && clause_allocator@[cref].code@ + cref + HEADER_LEN@ <= clause_allocator@.len()
        && clause_invariant(clause_allocator.get_clause_fset(cref), num_vars)
    }
}

// TODO: unpub buffer
pub(crate) struct ClauseAllocator {
    pub(crate) buffer: Vec<Lit>,
    pub(crate) num_vars: usize, // TODO: Look for a way to not have to store this everywhere
}

impl ClauseAllocator {
    #[open]
    #[logic]
    //#[ensures(forall<i: Int> 0 <= i && i < (self@.buffer).len() ==> (self@.buffer)[i] == (result@.buffer)[i])]
    //#[ensures(result@.num_vars == self.num_vars@)]
    pub(crate) fn push(self, lit: Lit) -> Self {
        self
    }

    #[open]
    #[predicate]
    pub(crate) fn extended(self, new: ClauseAllocator) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self.buffer@.len() ==> self.buffer@[i] == new.buffer@[i]
            && self.num_vars@ == new.num_vars@
            && self.buffer@.len() <= new.buffer@.len()
        }
    }
}

impl ClauseAllocator {
    #[open]
    #[predicate]
    pub(crate) fn inv(self) -> bool {
        pearlite! { self@.len() <= u32::MAX@ }
    }

    #[open]
    #[logic]
    //#[requires(cref_invariant(cref, self))]
    pub(crate) fn get_clause_logic(self, cref: Int) -> Seq<Lit> {
        pearlite! {
            self@.subsequence(cref + HEADER_LEN@, cref + HEADER_LEN@ + self@[cref].code@)
        }
    }

    #[open]
    #[logic]
    //#[requires(cref_invariant(cref, self))]
    pub(crate) fn get_clause_fset(self, cref: Int) -> FSet<Lit> {
        pearlite! {
            self.get_clause_fset_internal(cref, cref + HEADER_LEN@, cref + HEADER_LEN@ + self@[cref].code@)
        }
    }

    #[open]
    #[logic]
    //#[requires(cref_invariant(cref, self))]
    #[variant(upper - idx)]
    #[requires(idx >= 0 && upper <= self@.len())]
    fn get_clause_fset_internal(self, cref: Int, idx: Int, upper: Int) -> FSet<Lit> {
        pearlite! {
            if idx < upper {
                let set = self.get_clause_fset_internal(cref, idx + 1, upper);
                set.insert(self@[cref + idx])
            } else {
                FSet::EMPTY
            }
        }
    }
}

#[cfg(creusot)]
impl View for ClauseAllocator {
    type ViewTy = Seq<Lit>;

    #[open]
    #[logic]
    fn view(self) -> Self::ViewTy {
        self.buffer.view()
    }
}

pub const HEADER_LEN: usize = 1;

impl ClauseAllocator {
    // TODO: This is struggling with no_duplicate_indexes and FSet/Seq stuff
    #[maintains((mut self).inv())]
    #[requires(lits@.len() > 0)]
    #[requires(self@.len() + lits@.len() + HEADER_LEN@ <= u32::MAX@)] // TODO: May have to move this to a runtime check
    #[requires(clause_invariant_seq(lits@, self.num_vars@))]
    #[ensures((^self).num_vars == self.num_vars)]
    #[ensures((^self)@.len() == self@.len() + lits@.len() + HEADER_LEN@)]
    #[ensures(result@ == self@.len())]
    #[ensures((^self)@[result@].code@ == lits@.len())]
    #[ensures(forall<i: Int> 0 <= i && i < self@.len() ==> (^self)@[i] == self@[i])] // Head unchanged. TODO: Refactor ?
    #[ensures(forall<i: Int> 0 <= i && i < lits@.len() ==> (^self)@[result@ + HEADER_LEN@ + i] == lits@[i])] // Extended. TODO: Refactor ?
    #[ensures(cref_invariant(result@, ^self, self.num_vars@))]
    pub(crate) fn add_clause(&mut self, lits: &[Lit]) -> CRef {
        let cref = self.buffer.len() as CRef;
        self.buffer.push(Lit::raw(lits.len() as u32));

        let old_self: Snapshot<&mut ClauseAllocator> = snapshot!(self);

        #[invariant(self.num_vars == old_self.num_vars)] // TODO: Don't like this
        #[invariant(^*old_self == ^self)]
        #[invariant(self@.len() == old_self@.len() + produced.len())]
        #[invariant(forall<i: Int> 0 <= i && i < old_self@.len() ==> self@[i] == old_self@[i])] // TODO: Refactor ?
        #[invariant(forall<i: Int> 0 <= i && i < self@.len() - old_self@.len() ==>
                    self@[cref@ + HEADER_LEN@ + i] == lits@[i])]
        #[invariant(forall<i: Int> 0 <= i && i < self@.len() - old_self@.len() ==>
                    self@[cref@ + HEADER_LEN@ + i].var_in_range(self.num_vars@))]
        //#[invariant(forall<i: Int> 0 <= i && i < (produced).len() ==> self@[cref@ + HEADER_LEN@ + i] == *(produced)[i])]
        //#[invariant(forall<i: Int> 0 <= i && i < (produced).len() ==> self@[cref@ + HEADER_LEN@ + i] == (@lits)[i]
        //            && self@[cref@ + HEADER_LEN@ + i].var_in_range(self.num_vars@))]
        for lit in lits {
            self.buffer.push(*lit);
        }

        cref
    }

    #[requires(self.inv())]
    #[requires(cref_invariant(cref@, *self, self.num_vars@))]
    #[ensures(result@ == self.get_clause_logic(cref@))]
    pub(crate) fn get_clause(&self, cref: u32) -> &[Lit] {
        let idx = cref as usize;
        let len = self.buffer[idx].code as usize;
        &self.buffer[idx + HEADER_LEN..idx + HEADER_LEN + len]
    }
}
