extern crate creusot_contracts;
#[allow(unused)]
use creusot_contracts::{std::*, *};

use crate::{formula::*, util::*};

pub struct Decisions {
    pub lit_order: Vec<usize>,
}

impl Decisions {
    #[predicate]
    #[open]
    pub fn inv(self, n: Int) -> bool {
        pearlite! {
            self.lit_order@.len() == n
            && forall<i: Int> 0 <= i && i < self.lit_order@.len() ==>
               self.lit_order@[i]@ < n
        }
    }
}

impl Decisions {
    #[cfg_attr(feature = "trust_decision", trusted)]
    #[requires(f.inv())]
    #[ensures(result.inv(f.num_vars@))]
    pub fn new(f: &Formula) -> Decisions {
        let mut lit_order: Vec<usize> = vec::from_elem(0, f.num_vars);
        let mut counts: Vec<usize> = vec::from_elem(0, f.num_vars);
        let mut counts_with_index: Vec<(usize, usize)> = vec::from_elem((0, 0), f.num_vars);
        let mut i: usize = 0;
        #[invariant(counts@.len() == f.num_vars@)]
        while i < f.clauses.len() {
            let curr_clause = &f.clauses[i];
            let mut j: usize = 0;
            #[invariant(counts@.len() == f.num_vars@)]
            while j < curr_clause.rest.len() {
                // Okay this is obviously provable, a vector cannot be longer than usize, and we don't allow duplicates, so we will
                // never overflow, even if every clause contains a literal,
                // "ugly" runtime check. No way that a formula ever has more than 2^64 instances of a variable, but no way to guarantee
                // that it doesn't either. Runtime is not dominated by this function anyways, and it doesn't affect correctness.
                if counts[curr_clause.rest[j].idx] < usize::MAX {
                    counts[curr_clause.rest[j].idx] += 1;
                }
                j += 1;
            }
            i += 1;
        }
        i = 0;
        #[invariant(counts_with_index@.len() == f.num_vars@)]
        #[invariant(forall<j: Int> 0 <= j && j < f.num_vars@ ==>
            counts_with_index@[j].1@ < f.num_vars@)]
        while i < f.num_vars {
            counts_with_index[i] = (counts[i], i);
            i += 1;
        }
        sort_reverse(&mut counts_with_index);
        i = 0;
        #[invariant(lit_order@.len() == f.num_vars@)]
        #[invariant(forall<j: Int> 0 <= j && j < f.num_vars@ ==> lit_order@[j]@ < f.num_vars@)]
        while i < f.num_vars {
            lit_order[i] = counts_with_index[i].1;
            i += 1;
        }
        Decisions { lit_order: lit_order }
    }
}
