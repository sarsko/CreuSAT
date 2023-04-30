extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::{logic::FSet, std::*};

use crate::{assignments::*, lit::*};

#[predicate]
pub(crate) fn clause_sat(clause: FSet<Lit>, assignments: Seq<AssignedState>) -> bool {
    pearlite! {
        exists<l: _> clause.contains(l) && l.sat(assignments)
    }
}

#[predicate]
pub(crate) fn clause_invariant(clause: FSet<Lit>, num_vars: Int) -> bool {
    pearlite! {
        forall<l: _> clause.contains(l) ==> l.var_in_range(num_vars)
    }
}

#[predicate]
pub(crate) fn clause_invariant_seq(clause: Seq<Lit>, num_vars: Int) -> bool {
    pearlite! {
        // no_duplicate_indexes_inner(clause) &&
        forall<i: Int> 0 <= i && i < clause.len() ==> clause[i].var_in_range(num_vars)
    }
}

#[predicate]
pub(crate) fn no_duplicate_indexes_inner(clause: Seq<Lit>) -> bool {
    pearlite! {
        forall<j: Int, k: Int> 0 <= j && j < clause.len() &&
                0 <= k && k < j ==> !(clause[k].index_logic() == clause[j].index_logic())
    }
}
