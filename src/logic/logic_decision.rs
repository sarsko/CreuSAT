extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::decision::*;

impl Decisions {
    #[predicate]
    pub fn invariant(self, n: Int) -> bool {
        pearlite! {
            (@self.lit_order).len() === n &&
            forall<i: Int> 0 <= i && i < (@self.lit_order).len() ==>
                @(@self.lit_order)[i] < n
        }
    }
}
