extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::clause::*;

#[derive(Clone, Copy)]
pub struct Lit {
    pub idx: usize,
    pub polarity: bool,
}

impl Lit {
    #[predicate]
    pub fn lit_in(self, c: Clause) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@c).len() ==>
                (@c)[i] === self
        }
    }
}