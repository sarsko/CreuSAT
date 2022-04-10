extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::{
    formula::*,
    watches::*,
};

use crate::logic::{
    logic_util::*,
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
        true
        /*
        2 * n === w.len() &&
        forall<i: Int> 0 <= i && i < w.len() ==>
        forall<j: Int> 0 <= j && j < (@w[i]).len() ==>
            @(@w[i])[j].cref < (@f.clauses).len() && 
            (@(@f.clauses)[@(@w[i])[j].cref]).len() > 1
            */

    }
}

#[predicate]
pub fn watcher_crefs_in_range(w: Seq<Watcher>, f: Formula) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < w.len() ==>
            @w[j].cref < (@f.clauses).len() 
    }
}

#[predicate]
pub fn watches_crefs_in_range(w: Seq<Vec<Watcher>>, f: Formula) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < w.len() ==>
            watcher_crefs_in_range(@w[i], f)
    }
}

#[logic]
#[requires(w.len() > 0)]
#[requires(watcher_crefs_in_range(w, f))]
#[ensures(watcher_crefs_in_range(pop(w), f))]
pub fn lemma_pop_watch_maintains_watcher_invariant(w: Seq<Watcher>, f: Formula) {}

#[logic]
#[requires(watcher_crefs_in_range(w, f))]
#[requires(@o.cref < (@f.clauses).len())]
#[ensures(watcher_crefs_in_range(w.push(o), f))]
pub fn lemma_push_maintains_watcher_invariant(w: Seq<Watcher>, f: Formula, o: Watcher) {}

/*
#[requires(watches_crefs_in_range(w, f))]
#[requires(0 <= watchidx && watchidx < w.len())]
#[requires((@w[watchidx]).len() > 0)]
#[ensures(watches_crefs_in_range(w, f))]
pub fn lemma_pop_watch_maintains_invariant(w: Seq<Vec<Watcher>>, f: Formula, watchidx: Int) {
    lemma_pop_watch_maintains_watcher_invariant(w[watchidx], f);
}
*/

impl Watches {
    #[predicate]
    //#[ensures(result === watches_invariant_internal(@self.watches, n))]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            //watches_invariant_internal(@self.watches, n)
            2 * @f.num_vars === (@self.watches).len() &&
            forall<i: Int> 0 <= i && i < (@self.watches).len() ==>
                watcher_crefs_in_range(@(@self.watches)[i], f)
            //watches_crefs_in_range(@self.watches, f)
                /*&&
                ((@f.clauses)[@(@(@self.watches)[i])[j].cref].first.to_neg_watchidx_logic() === i ||
                (@f.clauses)[@(@(@self.watches)[i])[j].cref].second.to_neg_watchidx_logic() === i )
                */
                // Harder invariant, but might be needed

        }
    }
}
