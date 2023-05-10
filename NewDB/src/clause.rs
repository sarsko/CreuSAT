extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::{logic::FSet, std::*};

use crate::{assignments::*, lit::*};

pub(crate) struct ClauseFSet {
    pub(crate) lits: FSet<Lit>,
}

impl ClauseFSet {
    #[predicate]
    pub(crate) fn sat(self, assignments: AssignmentsModel) -> bool {
        pearlite! {
            exists<l: _> self.lits.contains(l) && l@.sat(assignments)
        }
    }

    // TODO: Change the clause to store the num_vars internally?
    #[predicate]
    pub(crate) fn invariant(self, num_vars: Int) -> bool {
        pearlite! {
            forall<l: _> self.lits.contains(l) ==> l@.var_in_range(num_vars)
        }
    }
}

// TODO: Impl Index?
pub struct ClauseSeq {
    pub(crate) lits: Seq<Lit>,
}

impl ClauseSeq {
    #[predicate]
    pub(crate) fn invariant(self, num_vars: Int) -> bool {
        pearlite! {
            // no_duplicate_indexes_inner(clause) &&
            forall<i: Int> 0 <= i && i < self.lits.len() ==> self.lits[i]@.var_in_range(num_vars)
        }
    }

    #[predicate]
    pub(crate) fn no_duplicate_indexes(self) -> bool {
        pearlite! {
            forall<j: Int, k: Int> 0 <= j && j < self.lits.len() &&
                    0 <= k && k < j ==> !(self.lits[k]@.index_logic() == self.lits[j]@.index_logic())
        }
    }
}
