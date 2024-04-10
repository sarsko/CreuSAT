extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{formula::*, watches::*};

use crate::logic::logic_util::*;

// The n is here so that we can "hijack" it during initialization
#[predicate]
#[open]
pub fn watches_invariant_internal(w: Seq<Vec<Watcher>>, n: Int, f: Formula) -> bool {
    pearlite! {
        2 * n == w.len()
        && forall<i: Int> 0 <= i && i < w.len() ==>
            forall<j: Int> 0 <= j && j < w[i]@.len() ==>
                   ((w[i]@[j].cref@ < f.clauses@.len()
                && f.clauses@[w[i]@[j].cref@]@.len() > 1)
                && w[i]@[j].blocker.index_logic() < f.num_vars@)
                //&& f.clauses@[@(@w[i])[j].cref].search_idx_in_range()
    }
}

// The watches for a specific literal are valid for a formula
#[predicate]
#[open]
pub fn watch_valid(w: Seq<Watcher>, f: Formula) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < w.len() ==>
                w[j].cref@ < f.clauses@.len() // all clauses are valid
            &&  f.clauses@[w[j].cref@]@.len() > 1 // the clauses have at least two litearls
            && w[j].blocker.index_logic() < f.num_vars@ // something about blocking lits
    }
}

#[predicate]
#[open]
pub fn watcher_crefs_in_range(w: Seq<Watcher>, f: Formula) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < w.len() ==>
            w[j].cref@ < f.clauses@.len()
    }
}

#[predicate]
#[open]
pub fn watches_crefs_in_range(w: Seq<Vec<Watcher>>, f: Formula) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < w.len() ==>
            watcher_crefs_in_range(w[i]@, f)
    }
}

#[logic]
#[open]
#[cfg_attr(feature = "trust_watches_logic", trusted)]
#[requires(w.len() > 0)]
#[requires(watcher_crefs_in_range(w, f))]
#[ensures(watcher_crefs_in_range(pop(w), f))]
pub fn lemma_pop_watch_maintains_watcher_invariant(w: Seq<Watcher>, f: Formula) {}

#[logic]
#[open]
#[cfg_attr(feature = "trust_watches_logic", trusted)]
#[requires(watcher_crefs_in_range(w, f))]
#[requires(o.cref@ < f.clauses@.len())]
#[ensures(watcher_crefs_in_range(w.push(o), f))]
pub fn lemma_push_maintains_watcher_invariant(w: Seq<Watcher>, f: Formula, o: Watcher) {}

impl Watches {
    #[predicate]
    #[open]
    //#[ensures(result == watches_invariant_internal(self.watches@, n))]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            watches_invariant_internal(self.watches@, f.num_vars@, f)
        }
    }
}
