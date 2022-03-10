extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

#[predicate]
pub fn ex(v: Vec<usize>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < (@v).len()
        true === true
            //(@v)[i] === (@v)[i]
    }
}