extern crate creusot_contracts;

use creusot_contracts::logic::FSet;
use creusot_contracts::{std::clone::Clone, std::*, vec, *};


use crate::{clause_allocator::*};
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
        && clause_allocator.get_clause_seq(cref).invariant(num_vars)
        //clause_allocator.buffer.subsequence(cref + HEADER_LEN@, cref + HEADER_LEN@ + self.buffer[cref].code)
    }
}

#[predicate]
pub(crate) fn cref_invariant_fset(cref: Int, clause_allocator: ClauseAllocatorModel, num_vars: Int) -> bool {
    pearlite! {
        0 <= cref && cref < clause_allocator.buffer.len()
        && clause_allocator.buffer[cref].code + cref + HEADER_LEN@ <= clause_allocator.buffer.len() // TODO: Do I need this?
        && clause_allocator.get_clause_fset(cref).invariant(num_vars)
    }
}