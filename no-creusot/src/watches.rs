use crate::formula::*;
use crate::lit::*;

// Lets try this scheme and see how well it fares
// Watches are indexed on 2 * lit.idx for positive and 2 * lit.idx + 1 for negative
#[derive(Debug)]
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
    pub fn new(num_vars: usize) -> Watches {
        let mut i = 0;
        let mut watches = Vec::new();
        while i < num_vars {
            watches.push(Vec::new());
            watches.push(Vec::new());
            i += 1;
        }
        Watches {watches}
    }

    // We watch the negated literal for updates
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
        let old = self.watches[old_idx].remove(i);
        self.watches[new_lit.to_neg_watchidx()].push(old);
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

    // The whole org of things should be better to make sure that len 0 and len 1 never occur, and len 2 should be treated as a special case
    pub fn init_watches(&mut self, f: &Formula) {
        let mut i = 0;
        while i < f.clauses.len() {
            let clause = &f.clauses[i].0;
            if clause.len() == 0 {
                panic!("Empty clause");
            }
            else if clause.len() == 1 {
                panic!("Unit clause");
            }
            let mut j = 0;
            while j < 2 {
                let lit = clause[j];
                self.add_watcher(lit, i);
                j += 1;
            }
            i += 1;
        }
        self.check_invariant(&"INIT"); // Debug assertion
        self.check_only_first_two_watched(f, &"RIGHT AFTER INIT"); // Debug assertion
    }
}