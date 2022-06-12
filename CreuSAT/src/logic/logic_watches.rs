extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{formula::*, watches::*};

use crate::logic::logic_util::*;

// The n is here so that we can "hijack" it during initialization
#[predicate]
pub fn watches_invariant_internal(w: Seq<Vec<Watcher>>, n: Int, f: Formula) -> bool {
    pearlite! {
        2 * n == w.len()
        && forall<i: Int> 0 <= i && i < w.len() ==>
            forall<j: Int> 0 <= j && j < (@w[i]).len() ==>
                   ((@(@w[i])[j].cref < (@f.clauses).len()
                && (@(@f.clauses)[@(@w[i])[j].cref]).len() > 1)
                && (@w[i])[j].blocker.index_logic() < @f.num_vars)
                //&& (@f.clauses)[@(@w[i])[j].cref].search_idx_in_range()
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
#[cfg_attr(feature = "trust_watches_logic", trusted)]
#[requires(w.len() > 0)]
#[requires(watcher_crefs_in_range(w, f))]
#[ensures(watcher_crefs_in_range(pop(w), f))]
pub fn lemma_pop_watch_maintains_watcher_invariant(w: Seq<Watcher>, f: Formula) {}

#[logic]
#[cfg_attr(feature = "trust_watches_logic", trusted)]
#[requires(watcher_crefs_in_range(w, f))]
#[requires(@o.cref < (@f.clauses).len())]
#[ensures(watcher_crefs_in_range(w.push(o), f))]
pub fn lemma_push_maintains_watcher_invariant(w: Seq<Watcher>, f: Formula, o: Watcher) {}

impl Watches {
    #[predicate]
    //#[ensures(result == watches_invariant_internal(@self.watches, n))]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            watches_invariant_internal(@self.watches, @f.num_vars, f)
            /*
            // WARNING: This below does not require length > 1
            2 * @f.num_vars == (@self.watches).len() &&
            forall<i: Int> 0 <= i && i < (@self.watches).len() ==>
                watcher_crefs_in_range(@(@self.watches)[i], f)
                */
            //watches_crefs_in_range(@self.watches, f)
                /*&&
                ((@f.clauses)[@(@(@self.watches)[i])[j].cref].first.to_neg_watchidx_logic() == i ||
                (@f.clauses)[@(@(@self.watches)[i])[j].cref].second.to_neg_watchidx_logic() == i )
                */
                // Harder invariant, but might be needed

        }
    }
}
