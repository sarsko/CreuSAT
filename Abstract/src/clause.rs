extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::{logic::FSet, std::*};

use crate::{assignments::*, lit::*};
use crate::logic_util::seq_to_fset;

/*
// Glucose representation of a Clause
class Clause {
    struct {
        unsigned mark : 2;
        unsigned learnt : 1;
        unsigned has_extra : 1;
        unsigned reloced : 1;
        unsigned canbedel : 1;
        unsigned location : 2;
        unsigned simplified : 1;
        unsigned exported : 2;
        unsigned lbd : 21;
        unsigned imported : 1;
        unsigned oneWatched : 1;
        unsigned size : 30;
    } header;
    union {
        Lit      lit;
        float    act;
        uint32_t abs;
        uint32_t touched;
        CRef     rel;
    } data[0];
}
*/

pub(crate) struct ClauseFSet {
    pub(crate) lits: FSet<LitModel>,
}

impl ClauseFSet {
    #[predicate]
    pub(crate) fn sat(self, assignments: AssignmentsModel) -> bool {
        pearlite! {
            exists<l: _> self.lits.contains(l) && l.sat(assignments)
        }
    }

    // TODO: Change the clause to store the num_vars internally?
    #[predicate]
    pub(crate) fn invariant(self, num_vars: Int) -> bool {
        pearlite! {
            forall<l: _> self.lits.contains(l) ==> l.var_in_range(num_vars)
        }
    }
}

// TODO: Impl Index?
pub struct ClauseSeq {
    pub(crate) lits: Seq<LitModel>,
}

impl ClauseSeq {
    // TODO: Actually calc the header
    #[logic]
    #[ensures(0 <= result)]
    pub(crate) fn calc_header(self) -> Int {
        0
    }


    #[logic]
    #[ensures(0 <= result)]
    #[ensures(result == self.lits.len())]
    pub(crate) fn len(self) -> Int {
        self.lits.len()
    }

    #[logic]
    pub(crate) fn to_fset(self) -> ClauseFSet {
        ClauseFSet { lits: seq_to_fset(self.lits) }
    }
}

impl ClauseSeq {
    #[predicate]
    pub(crate) fn invariant(self, num_vars: Int) -> bool {
        pearlite! {
            // no_duplicate_indexes_inner(clause) &&
            forall<i: Int> 0 <= i && i < self.lits.len() ==> self.lits[i].var_in_range(num_vars)
        }
    }

    // TODO: Not currently in use. Unsure whether it is needed.
    #[predicate]
    pub(crate) fn no_duplicate_indexes(self) -> bool {
        pearlite! {
            forall<j: Int, k: Int> 0 <= j && j < self.lits.len() &&
                    0 <= k && k < j ==> !(self.lits[k].index_logic() == self.lits[j].index_logic())
        }
    }
}
