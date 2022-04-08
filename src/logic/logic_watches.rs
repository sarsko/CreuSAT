extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::{
    formula::*,
    watches::*,
};

#[predicate]
pub fn watches_invariant_internal(w: Seq<Vec<Watcher>>, n: Int) -> bool {
    pearlite! {
        2 * n === w.len() 
    }
}

#[predicate]
pub fn watches_invariant_internal2(w: Seq<Vec<Watcher>>, n: Int, f: Formula) -> bool {
    pearlite! {
        2 * n === w.len() &&
        forall<i: Int> 0 <= i && i < w.len() ==>
        forall<j: Int> 0 <= j && j < (@w[i]).len() ==>
            @(@w[i])[j].cref < (@f.clauses).len() && 
            (@(@f.clauses)[@(@w[i])[j].cref]).len() > 1
    }
}

impl Watches {
    #[predicate]
    //#[ensures(result === watches_invariant_internal(@self.watches, n))]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            //watches_invariant_internal(@self.watches, n)
            2 * @f.num_vars === (@self.watches).len() &&
            forall<i: Int> 0 <= i && i < (@self.watches).len() ==>
            forall<j: Int> 0 <= j && j < (@(@self.watches)[i]).len() ==>
                @(@(@self.watches)[i])[j].cref < (@f.clauses).len() 
                /*&&
                ((@f.clauses)[@(@(@self.watches)[i])[j].cref].first.to_neg_watchidx_logic() === i ||
                (@f.clauses)[@(@(@self.watches)[i])[j].cref].second.to_neg_watchidx_logic() === i )
                */
                // Harder invariant, but might be needed

        }
    }
}