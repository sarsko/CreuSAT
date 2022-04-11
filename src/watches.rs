extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::{
    formula::*,
    lit::*,
    assignments::*,
    trail::*,
    clause::*,
};

#[cfg(contracts)]
use crate::logic::{
    logic_watches::*,
    logic_util::*,
};


// Lets try this scheme and see how well it fares
// Watches are indexed on 2 * lit.idx for positive and 2 * lit.idx + 1 for negative
pub struct Watcher {
    pub cref: usize,
    //blocker: Lit,
}

pub struct Watches {
    pub watches: Vec<Vec<Watcher>>,
}

// Should probably move this into Watches
// Much ahoy for nothing?
// Added a bunch of assertions and lemmas in an attempt to make it faster, but it helped less than desired(still needed for the current encoding)
// The root cause seems to be that Why3 doesn't wan't to "peek" into things, so when I made abstraction
// barriers for the invariants, stuff took forever. It checks out, but I should probably come back later and clean up
#[cfg_attr(all(any(trust_watch, trust_all), not(untrust_all)), trusted)]
//#[requires(watches.invariant(*f))]
//#[ensures((^watches).invariant(*f))]
#[maintains((mut watches).invariant(*f))]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(@lit.idx < @f.num_vars)]
//#[requires(trail.trail_sem_invariant(*f, *a))]
//#[requires(trail.assignments.invariant(*f))]
#[requires(f.invariant())]
#[requires(trail.invariant(*f))]
//#[requires((@trail.trail).len() > 0)]
#[requires(@cref < (@f.clauses).len())]
#[requires(0 <= @k && @k < (@(@f.clauses)[@cref]).len())] // Changed
#[requires((@(@f.clauses)[@cref]).len() >= 2)] // This was > 2 before ?
//#[requires((@(@watches.watches)[lit.to_watchidx_logic()]).len() > 0)]  // removed since last run, but shoudln't matter
#[requires((@(@watches.watches)[lit.to_watchidx_logic()]).len() > @j)]
//#[ensures(trail.trail_sem_invariant(*f, *a))]
//#[ensures((*f).invariant())]
//#[ensures(trail.invariant(*f))]
//#[ensures(a.invariant(*f))]
pub fn update_watch(f: &Formula, trail: &Trail, watches: &mut Watches, cref: usize, j: usize, k: usize, lit: Lit) {
    let watchidx = lit.to_watchidx();
    let end = watches.watches[watchidx].len() - 1;
    watches.watches[watchidx].swap(j, end);
    let curr_lit = f.clauses[cref].rest[k];
    //watches.move_to_end(watchidx, j, curr_lit, f);
    proof_assert!(@watchidx < (@watches.watches).len());
    let old_w = Ghost::record(&watches);
    //proof_assert!(watcher_crefs_in_range((@(@(@old_w).watches)[@watchidx]), *f));
    proof_assert!((@old_w).watches === watches.watches);
    proof_assert!(watcher_crefs_in_range(@(@watches.watches)[@watchidx], *f));
    match watches.watches[watchidx].pop() {
        Some(w) => {
            proof_assert!(^@old_w === ^watches);
            proof_assert!(lemma_pop_watch_maintains_watcher_invariant(@(@(@old_w).watches)[@watchidx], *f); true);
            proof_assert!(watcher_crefs_in_range(pop(@(@(@old_w).watches)[@watchidx]), *f));
            proof_assert!(@(@watches.watches)[@watchidx] === pop(@(@(@old_w).watches)[@watchidx]));
            proof_assert!(watcher_crefs_in_range(@(@watches.watches)[@watchidx], *f));
            proof_assert!(watches.invariant(*f));
            proof_assert!(curr_lit.to_neg_watchidx_logic() < (@watches.watches).len());

            proof_assert!(watcher_crefs_in_range(@(@watches.watches)[curr_lit.to_neg_watchidx_logic()], *f));
            proof_assert!(@w.cref < (@f.clauses).len());
            proof_assert!(lemma_push_maintains_watcher_invariant(@(@watches.watches)[curr_lit.to_neg_watchidx_logic()], *f, w); true);
            watches.watches[curr_lit.to_neg_watchidx()].push(w);
            proof_assert!(watcher_crefs_in_range(@(@watches.watches)[curr_lit.to_neg_watchidx_logic()], *f));
            proof_assert!(watches.invariant(*f));
        },
        None => {
            panic!("Impossible");
        }
    }
}


impl Watches {
    // The way clauses are made and added should really be changed - builder pattern?
    // OK
    #[cfg_attr(all(any(trust_watch, trust_all), not(untrust_all)), trusted)]
    #[ensures(result.invariant(*f))]
    pub fn new(f: &Formula) -> Watches {
        let mut i: usize = 0;
        let mut watches = Vec::new();
        #[invariant(i_less, @i <= @f.num_vars)]
        #[invariant(maintains_inv, watches_invariant_internal(@watches, @i, *f))]
        while i < f.num_vars {
            watches.push(Vec::new());
            watches.push(Vec::new());
            i += 1;
        }
        Watches { watches }
    }

    // This whole should be updated/merged with formula add_clause
    // We watch the negated literal for updates
    // OK
    #[cfg_attr(all(any(trust_watch, trust_all), not(untrust_all)), trusted)]
    #[maintains((mut self).invariant(*_f))]
    #[requires(@cref < (@_f.clauses).len())]
    #[requires(@lit.idx < @usize::MAX/2)]
    #[requires(lit.to_neg_watchidx_logic() < (@self.watches).len())]
    #[ensures((@self.watches).len() === (@(^self).watches).len())]
    pub fn add_watcher(&mut self, lit: Lit, cref: usize, _f: &Formula) {
        self.watches[lit.to_neg_watchidx()].push(Watcher { cref });
    }

    // OK
    #[cfg_attr(all(any(trust_watch, trust_all), not(untrust_all)), trusted)]
    #[maintains((mut self).invariant(*_f))]
    #[requires(@new_lit.idx < @usize::MAX/2)]
    #[requires(new_lit.to_neg_watchidx_logic() < (@self.watches).len())]
    #[requires(@old_idx < (@self.watches).len())]
    #[requires(@old_pos < (@(@self.watches)[@old_idx]).len())]
    #[ensures((@(@(^self).watches)[@old_idx]).len() === ((@(@self.watches)[@old_idx]).len()))]
    pub fn move_to_end(&mut self, old_idx: usize, old_pos: usize, new_lit: Lit, _f: &Formula) {
        let end = self.watches[old_idx].len() - 1;
        self.watches[old_idx].swap(old_pos, end);
    }

    // Requires duplicates to be removed
    // OK
    #[cfg_attr(all(any(trust_watch, trust_all), not(untrust_all)), trusted)]
    #[maintains((mut self).invariant(*f))]
    #[requires(@f.num_vars < @usize::MAX/2)]
    #[requires(f.invariant())]
    pub fn init_watches(&mut self, f: &Formula) {
        let old_w = Ghost::record(&self); 
        let mut i = 0;
        //#[invariant(watchidx, f.idxs_in_range())]  // #[trusted] // OK
        #[invariant(watch_inv, self.invariant(*f))]
        #[invariant(same_len, (@self.watches).len() === 2 * @f.num_vars)]
        #[invariant(proph, ^self === ^@old_w)]
        while i < f.clauses.len() {
            let clause = &f.clauses[i];
            self.add_watcher(clause.rest[0], i, f);
            self.add_watcher(clause.rest[1], i, f);
            i += 1;
        }
    }
}