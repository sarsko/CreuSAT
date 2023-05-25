use crate::{formula::*, lit::*, solver::*, clause_manager::clause_manager::ClauseManager};
use crate::clause_manager::common::CRef;
use std::{ops::{Index, IndexMut}};

// Lets try this scheme and see how well it fares
// Watches are indexed on 2 * lit.idx for positive and 2 * lit.idx + 1 for negative
pub(crate) struct Watcher {
    pub cref: CRef,
    pub blocker: Lit,
}

pub(crate) struct Watches {
    watches: Vec<Vec<Watcher>>,
}

impl Index<usize> for Watches {
    type Output = Vec<Watcher>;
    #[inline]
    fn index(&self, i: usize) -> &Vec<Watcher> {
        //#[cfg(feature = "unsafe_access")]
        unsafe { self.watches.get_unchecked(i) }
        //#[cfg(not(feature = "unsafe_access"))]
        //&self.watches[i]
    }
}

impl IndexMut<usize> for Watches {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut Vec<Watcher> {
        //#[cfg(feature = "unsafe_access")]
        unsafe { self.watches.get_unchecked_mut(i) }
        //#[cfg(not(feature = "unsafe_access"))]
        //&mut self.watches[i]
    }
}

#[inline]
pub(crate) fn update_watch(lits: &[Lit], watches: &mut Watches, j: usize, k: usize, lit: Lit) {
    let watchidx = lit.to_watchidx();
    let end = watches.watches[watchidx].len() - 1;
    watches.watches[watchidx].swap(j, end);
    let curr_lit = lits[k];
    match watches.watches[watchidx].pop() {
        Some(w) => {
            watches.watches[curr_lit.to_neg_watchidx()].push(w);
        }
        None => {
            unreachable!();
        }
    }
}

impl Watches {
    #[inline]
    fn len(&self) -> usize {
        self.watches.len()
    }

    pub(crate) fn new(num_vars: usize) -> Watches {
        let mut i: usize = 0;
        let mut watches = Vec::new();
        while i < num_vars {
            watches.push(Vec::new());
            watches.push(Vec::new());
            i += 1;
        }
        Watches { watches }
    }

    pub(crate) fn init_watches(&mut self, clause_manager: &ClauseManager) {
        let mut i = 0;
        for cref in clause_manager.original_crefs() {
            let clause = &clause_manager.get_clause(*cref);
            if clause.len() > 1 {
                self[clause[0].to_neg_watchidx()].push(Watcher { cref: *cref, blocker: clause[1] });
                self[clause[1].to_neg_watchidx()].push(Watcher { cref: *cref, blocker: clause[0] });
            }
            i += 1;
        }
    }

    #[inline]
    pub(crate) fn unwatch(&mut self, cref: CRef, lit: Lit) {
        let watchidx = lit.to_neg_watchidx();
        let mut i: usize = 0;
        while i < self[watchidx].len() {
            if self[watchidx][i].cref == cref {
                self[watchidx].swap_remove(i);
                /*
                let end = self.watches[watchidx].len() - 1;
                self.watches[watchidx].swap(i, end);
                self.watches[watchidx].pop();
                */
                /*
                match self.watches[watchidx].pop() {
                    Some(w) => {
                    }
                    None => {
                        unreachable!();
                    }
                }
                */
                return;
            }
            i += 1;
        }
    }

    #[inline]
    pub(crate) fn unwatch_all_lemmas(&mut self, s: &Solver) {
        let mut i: usize = 0;
        while i < self.len() {
            let mut j = 0;
            while j < self[i].len() {
                if self[i][j].cref > s.initial_len - 1 {
                    self[i].swap_remove(j);
                    //let end = self.watches[i].len() - 1;
                    //self.watches[i].swap(j, end);
                    //self.watches[i].pop();
                } else {
                    j += 1;
                }
            }
            i += 1;
        }
    }
}
