use crate::formula::*;
use crate::lit::*;
use crate::assignments::*;
use crate::trail::*;
use crate::solver::*; // TODO move

// Lets try this scheme and see how well it fares
// Watches are indexed on 2 * lit.idx for positive and 2 * lit.idx + 1 for negative
#[derive(Debug, Clone)]
pub struct Watcher {
    pub cref: usize,
    //blocker: Lit,
}

#[derive(Debug)]
pub struct Watches {
    pub watches: Vec<Vec<Watcher>>,
}

impl Watches {
    // The way clauses are made and added should really be changed - builder pattern?
    #[inline]
    pub fn new(num_vars: usize) -> Watches {
        let watches = vec![vec![]; 2 * num_vars];
        Watches { watches }
    }

    // We watch the negated literal for updates
    #[inline]
    pub fn add_watcher(&mut self, lit: Lit, cref: usize) {
        self.watches[lit.to_neg_watchidx()].push(Watcher {cref});
    }

    // This requires the literal to be watched, otherwise it will panic
    // This method should be updated as we usually know where to look
    pub fn update_watch(&mut self, old_lit: Lit, new_lit: Lit, cref: usize) {
        //assert!(old_lit != new_lit);
        let mut i = 0;
        let old_idx = old_lit.to_watchidx();
        while i < self.watches[old_idx].len() {
            if self.watches[old_idx][i].cref == cref {
                break;
            }
            i += 1;
        }
        //assert!(self.watches[old_idx][i].cref == cref);

        //self.check_invariant("UPDATE_BEFORE");
        // Okay so it seems like the swap and pop is actually marginally faster than both the remove and the swap_remove. Nice
        let end = self.watches[old_idx].len() - 1;
        self.watches[old_idx].swap(i, end);
        match self.watches[old_idx].pop() {
            Some(w) => {
                self.watches[new_lit.to_neg_watchidx()].push(w);
            },
            None => {
                unreachable!();
            }
        }
        //let old = self.watches[old_idx].swap_remove(i);
        //self.watches[new_lit.to_neg_watchidx()].push(old);
        //let old = self.watches[old_idx].remove(i);
        //self.watches[new_lit.to_neg_watchidx()].push(old);
        //self.check_invariant("UPDATE_AFTER");
    }

    // Debug function that checks that all the watches are for one of the first two literals of each clause
    pub fn check_only_first_two_watched(&self, f: &Formula, s: &str) {
        let mut i = 0;
        while i < self.watches.len() {
            let mut j = 0;
            while j < self.watches[i].len() {
                let cref = self.watches[i][j].cref;
                let lit_idx = i / 2;
                if f.clauses[cref].0[0].idx != lit_idx && f.clauses[cref].0[1].idx != lit_idx {
                    panic!("{}\n
                    There exists a watched literal which is not one of the first two literals in the clause!\n
                    Clause: {:?}\n
                    Index: {}\n", s, f.clauses[cref].0, lit_idx);
                }
                j += 1;
            }
            i += 1;
        }
    }

    // Debug function to check that the watchlist is correct
    // Doesnt check that all are watched or that the watched lits are the first in the clause
    pub fn check_invariant(&self, s: &str) {
        use std::collections::HashMap;
        let mut seen = HashMap::new();
        // Check that each literal only has two watches
        for i in 0..self.watches.len() {
            for j in 0..self.watches[i].len() {
                let cref = self.watches[i][j].cref;
                if seen.contains_key(&cref) {
                    if seen[&cref] > 1 {
                        panic!("{}\nThere exists more than two watched literals for the clause with cref: {:?}", s, cref);
                    }
                    seen.insert(cref, seen[&cref] + 1);
                }
                else { 
                    seen.insert(cref, 1);
                }
            }
        }
        // Check for 2 of the same watched literal for each clause
        for i in 0..self.watches.len() {
            let mut seen = HashMap::new();
            for j in 0..self.watches[i].len() {
                let cref = self.watches[i][j].cref;
                if seen.contains_key(&cref) {
                    panic! ("{}\nThere exists duplicate watching of the same literal for the clause with cref: {:?}", s, cref);
                }
                else { 
                    seen.insert(cref, 1);
                }
            }
        }
    }

    // Returns false if there exists an empty clause or two unit clauses of the same
    // literal with opposite polarity(exists a clause [[-l]] and [[l]] for some l)
    pub fn init_watches(&mut self, f: &Formula, trail: &mut Trail, a: &mut Assignments) -> bool {
        let mut i = 0;
        while i < f.clauses.len() {
            let clause = &f.clauses[i].0;
            if clause.len() == 0 {
                return false;
            } else if clause.len() == 1 {
                if a.0[clause[0].idx] == 2 {
                    learn_unit(a, trail, clause[0]);
                } else {
                    return false;
                }
            } else {
                self.add_watcher(clause[0], i);
                self.add_watcher(clause[1], i);
            }
            i += 1;
        }
        //self.check_invariant(&"INIT"); // Debug assertion
        //self.check_only_first_two_watched(f, &"RIGHT AFTER INIT"); // Debug assertion
        return true;
    }
}