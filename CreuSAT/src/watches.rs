use creusot_contracts::{std::*, Snapshot, *};

use crate::{formula::*, lit::*, trail::*};

#[cfg(creusot)]
use crate::logic::{logic_util::*, logic_watches::*};

// Lets try this scheme and see how well it fares
// Watches are indexed on 2 * lit.idx for positive and 2 * lit.idx + 1 for negative
pub struct Watcher {
    pub cref: usize,
    pub blocker: Lit,
}

pub struct Watches {
    pub watches: Vec<Vec<Watcher>>,
}

// Should probably move this into Watches
// Much ahoy for nothing?
// Added a bunch of assertions and lemmas in an attempt to make it faster, but it helped less than desired(still needed for the current encoding)
// The root cause seems to be that Why3 doesn't wan't to "peek" into things, so when I made abstraction
// barriers for the invariants, stuff took forever. It checks out, but I should probably come back later and clean up
// #10 and #19 just take some time, but check out on Mac
#[cfg_attr(all(feature = "trust_watches", not(feature = "problem_child")), trusted)]
#[maintains((mut watches).inv(*f))]
#[requires(f.num_vars@ < usize::MAX@/2)]
#[requires(lit.index_logic() < f.num_vars@)]
#[requires(f.inv())]
#[requires(trail.inv(*f))]
#[requires(cref@ < f.clauses@.len())]
#[requires(0 <= k@ && k@ < f.clauses@[cref@]@.len())] // Changed
#[requires(f.clauses@[cref@]@.len() >= 2)] // This was > 2 before ?
#[requires(watches.watches@[lit.to_watchidx_logic()]@.len() > j@)]
pub fn update_watch(f: &Formula, trail: &Trail, watches: &mut Watches, cref: usize, j: usize, k: usize, lit: Lit) {
    let watchidx = lit.to_watchidx();
    let end = watches.watches[watchidx].len() - 1;
    watches.watches[watchidx].swap(j, end);
    let curr_lit = f[cref][k];
    proof_assert!(watchidx@ < watches.watches@.len());
    let old_w: Snapshot<&mut Watches> = snapshot!(watches);
    proof_assert!(watcher_crefs_in_range(watches.watches@[watchidx@]@, *f));
    match watches.watches[watchidx].pop() {
        Some(w) => {
            proof_assert!(lemma_pop_watch_maintains_watcher_invariant(old_w.watches@[watchidx@]@, *f); true);
            proof_assert!(watches.watches@[watchidx@]@ == pop(old_w.watches@[watchidx@]@));
            proof_assert!(watcher_crefs_in_range(watches.watches@[watchidx@]@, *f));
            proof_assert!(watches.inv(*f));
            proof_assert!(curr_lit.to_neg_watchidx_logic() < watches.watches@.len());
            proof_assert!(watcher_crefs_in_range(watches.watches@[curr_lit.to_neg_watchidx_logic()]@, *f));
            proof_assert!(w.cref@ < f.clauses@.len());
            proof_assert!(lemma_push_maintains_watcher_invariant(watches.watches@[curr_lit.to_neg_watchidx_logic()]@, *f, w); true);

            let watch_lit = curr_lit.to_neg_watchidx();
            watches.watches[watch_lit].push(w);

            proof_assert!(watch_valid(watches.watches@[watch_lit@]@, *f));
            proof_assert!(watcher_crefs_in_range(watches.watches@[curr_lit.to_neg_watchidx_logic()]@, *f));
            proof_assert!(watches.inv(*f));
        }
        None => {
            unreachable!();
        }
    }
}

impl Watches {
    // OK
    #[cfg_attr(feature = "trust_watches", trusted)]
    #[ensures(result.inv(*f))]
    pub fn new(f: &Formula) -> Watches {
        let mut i: usize = 0;
        let mut watches = Vec::new();
        #[invariant(i@ <= f.num_vars@)]
        #[invariant(watches_inv_internal(watches@, i@, *f))]
        while i < f.num_vars {
            watches.push(Vec::new());
            watches.push(Vec::new());
            i += 1;
        }
        Watches { watches }
    }

    /*
    // This whole should be updated/merged with formula add_clause
    // We watch the negated literal for updates
    // OK
    #[cfg_attr(feature = "trust_watches", trusted)]
    #[maintains((mut self).inv(*_f))]
    #[requires(cref@ < (_f.clauses@).len())]
    #[requires(lit.index_logic() < usize::MAX@/2)]
    #[requires(lit.to_neg_watchidx_logic() < (self@.watches).len())]
    #[requires((@(_f.clauses@)[cref@]).len() > 1)]
    #[ensures((self@.watches).len() == (@(^self).watches).len())]
    pub fn add_watcher(&mut self, lit: Lit, cref: usize, _f: &Formula) {
        self.watches[lit.to_neg_watchidx()].push_back(Watcher { cref });
    }
    */

    #[cfg_attr(feature = "trust_watches", trusted)]
    #[maintains((mut self).inv(*_f))]
    #[requires(cref@ < _f.clauses@.len())]
    #[requires(lit.index_logic() < usize::MAX@/2)]
    #[requires(blocker.index_logic() < _f.num_vars@)]
    #[requires(lit.to_neg_watchidx_logic() < self.watches@.len())]
    #[requires(_f.clauses@[cref@]@.len() > 1)]
    #[ensures(self.watches@.len() == (^self).watches@.len())]
    pub fn add_watcher(&mut self, lit: Lit, cref: usize, _f: &Formula, blocker: Lit) {
        self.watches[lit.to_neg_watchidx()].push(Watcher { cref, blocker });
    }

    // OK
    #[cfg_attr(feature = "trust_watches", trusted)]
    #[maintains((mut self).inv(*_f))]
    #[requires(new_lit.index_logic() < usize::MAX@/2)]
    #[requires(new_lit.to_neg_watchidx_logic() < self.watches@.len())]
    #[requires(old_idx@ < self.watches@.len())]
    #[requires(old_pos@ < self.watches@[old_idx@]@.len())]
    #[ensures((^self).watches@[old_idx@]@.len() == self.watches@[old_idx@]@.len())]
    pub fn move_to_end(&mut self, old_idx: usize, old_pos: usize, new_lit: Lit, _f: &Formula) {
        let end = self.watches[old_idx].len() - 1;
        self.watches[old_idx].swap(old_pos, end);
    }

    // Requires duplicates to be removed
    // OK
    #[cfg_attr(feature = "trust_watches", trusted)]
    #[maintains((mut self).inv(*f))]
    #[requires(f.num_vars@ < usize::MAX@/2)]
    #[requires(f.inv())]
    pub fn init_watches(&mut self, f: &Formula) {
        let old_w: Snapshot<&mut Watches> = snapshot! { self };
        let mut i = 0;
        #[invariant(self.inv(*f))]
        #[invariant(self.watches@.len() == 2 * f.num_vars@)]
        while i < f.clauses.len() {
            let clause = &f[i];
            if clause.len() > 1 {
                //self.add_watcher(clause.rest[0], i, f);
                //self.add_watcher(clause.rest[1], i, f);
                self.watches[clause[0].to_neg_watchidx()].push(Watcher { cref: i, blocker: clause[1] });
                self.watches[clause[1].to_neg_watchidx()].push(Watcher { cref: i, blocker: clause[0] });
            }
            i += 1;
        }
    }

    // This is just the first half of update_watch.
    #[cfg_attr(all(feature = "trust_watches", not(feature = "problem_child")), trusted)]
    #[maintains((mut self).inv(*f))]
    #[requires(f.num_vars@ < usize::MAX@/2)]
    #[requires(lit.index_logic() < f.num_vars@)]
    #[requires(f.inv())]
    #[requires(trail.inv(*f))]
    #[requires(cref@ < f.clauses@.len())]
    #[requires(f.clauses@[cref@]@.len() >= 2)]
    pub fn unwatch(&mut self, f: &Formula, trail: &Trail, cref: usize, lit: Lit) {
        let watchidx = lit.to_neg_watchidx();
        let mut i: usize = 0;
        #[invariant(self.inv(*f))]
        while i < self.watches[watchidx].len() {
            if self.watches[watchidx][i].cref == cref {
                let end = self.watches[watchidx].len() - 1;
                self.watches[watchidx].swap(i, end);

                // TODO
                // Ugly "Snapshot" match. Grr.
                let old_w: Snapshot<&mut Watches> = snapshot! { self };
                match self.watches[watchidx].pop() {
                    Some(w) => {
                        proof_assert!(^old_w.inner() == ^self);
                        proof_assert!(self.inv(*f));
                    }
                    None => unreachable!(),
                }
                return;
            }
            i += 1;
        }
    }
}
