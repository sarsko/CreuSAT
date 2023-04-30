extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::decision::*;

impl Decisions {
    #[predicate]
    pub fn invariant(self, n: Int) -> bool {
        pearlite! {
            (self@.linked_list).len() == n
            && (self@.search < (self@.linked_list).len() || self@.search == usize::MAX@)
            && self@.start < (self@.linked_list).len()
            && forall<i: Int> 0 <= i && i < (self@.linked_list).len() ==>
                  ((@(self@.linked_list)[i].next == usize::MAX@ || @(self@.linked_list)[i].next < n)
                && (@(self@.linked_list)[i].prev == usize::MAX@ || @(self@.linked_list)[i].prev < n))
        }
    }
}
