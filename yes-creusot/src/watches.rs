extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::formula::*;
use crate::lit::*;
use crate::assignments::*;
use crate::trail::*;
use crate::solver::*; // TODO move


//use crate::ghost;

// Lets try this scheme and see how well it fares
// Watches are indexed on 2 * lit.idx for positive and 2 * lit.idx + 1 for negative
pub struct Watcher {
    pub cref: usize,
    //blocker: Lit,
}

pub struct Watches {
    pub watches: Vec<Vec<Watcher>>,
}

#[predicate]
pub fn watches_invariant_internal(w: Seq<Vec<Watcher>>, n: Int) -> bool {
    pearlite! {
        2 * n === w.len()
    }
}

impl Watches {
    #[predicate]
    //#[ensures(result === watches_invariant_internal(@self.watches, n))]
    pub fn invariant(self, n: Int) -> bool {
        pearlite! {
            //watches_invariant_internal(@self.watches, n)
            2 * n === (@self.watches).len()
        }
    }
}

impl Watches {
    // The way clauses are made and added should really be changed - builder pattern?
    #[ensures(result.invariant(@num_vars))]
    pub fn new(num_vars: usize) -> Watches {
        let mut i: usize = 0;
        let mut watches = Vec::new();
        #[invariant(maintains_inv, watches_invariant_internal(@watches, @i))]
        #[invariant(i_less, @i <= @num_vars)]
        while i < num_vars {
            watches.push(Vec::new());
            watches.push(Vec::new());
            i += 1;
        }
        Watches { watches }
    }

    // We watch the negated literal for updates
    //#[trusted] // TODO
    //#[requires(self.invariant(TODO))]
    //#[ensures((^self).invariant(TODO))]
    #[requires(@lit.idx < @usize::MAX/2)]
    #[requires(lit.to_neg_watchidx_logic() < (@self.watches).len())]
    #[ensures((@self.watches).len() === (@(^self).watches).len())]
    pub fn add_watcher(&mut self, lit: Lit, cref: usize) {
        self.watches[lit.to_neg_watchidx()].push(Watcher { cref });
    }

    // This requires the literal to be watched, otherwise it will panic
    // This method should be updated as we usually know where to look
    #[requires(!(old_lit === new_lit))]
    #[requires(@old_lit.idx < @usize::MAX/2)]
    #[requires(@new_lit.idx < @usize::MAX/2)]
    #[requires(old_lit.to_watchidx_logic() < (@self.watches).len())]
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

        // TODO !
        //let old = self.watches[old_idx].remove(i);
        //self.watches[new_lit.to_neg_watchidx()].push(old);

        //self.check_invariant("UPDATE_AFTER");
    }

    /*
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
    */

    /*
    */
    // Requires duplicates to be removed
    // Returns false if there exists an empty clause or two unit clauses of the same
    // literal with opposite polarity(exists a clause [[-l]] and [[l]] for some l) (this is true only when duplicates are removed)
    // Also returns false if there exists an empty clause
    // #[requires(no_duplicates)] // TODO
    #[trusted] // REMOVE
    #[requires(@f.num_vars < @usize::MAX/2)]
    #[requires(self.invariant(@f.num_vars))]
    #[requires(f.invariant())]
    #[requires(a.invariant(@f.num_vars))]
    #[requires(trail.invariant(@f.num_vars))]
    #[ensures((^trail).invariant(@f.num_vars))]
    #[ensures((^self).invariant(@f.num_vars))]
    #[ensures((^a).invariant(@f.num_vars))]
    #[ensures((@self.watches).len() === (@(^self).watches).len())]
    #[ensures((@(^trail).trail).len() === 1)]
    pub fn init_watches(&mut self, f: &Formula, trail: &mut Trail, a: &mut Assignments) -> bool {
        let mut i = 0;
        let old_self = Ghost::record(&self);
        #[invariant(same_len, (@(*self).watches).len() === (@(*@old_self).watches).len())]
        #[invariant(maintains_invariant, self.invariant(@f.num_vars))]
        #[invariant(intact, ^self === ^@old_self)]
        while i < f.clauses.len() {
            let clause = &f.clauses[i].0;
            if clause.len() == 0 {
                return false;
            } else if clause.len() == 1 {
                let bing = a.0[clause[0].idx];
                match bing {
                Some(_) => { return false; },
                    None => { 
                        let lit = clause[0];
                        //proof_assert! { ((@trail.trail).len() > 0) } // This is partially wrong
                        proof_assert! { (0 <= @lit.idx && @lit.idx < (@trail.vardata).len()) }
                        proof_assert! { (0 <= @lit.idx && @lit.idx < (@a).len()) }
                        proof_assert! { (trail.invariant((@trail.vardata).len())) }
                        proof_assert! { (a.invariant((@trail.vardata).len())) }
                        //learn_unit(a, trail, lit);
                    }
                }
            } else {
                let mut j = 0;
                #[invariant(maintains_invariant, self.invariant(@f.num_vars))]
                #[invariant(same_len, (@(*self).watches).len() === (@(*@old_self).watches).len())]
                #[invariant(intact, ^self === ^@old_self)]
                while j < 2 {
                    let lit = clause[j];
                    self.add_watcher(lit, i);
                    j += 1;
                }
            }
            i += 1;
        }
        //self.check_invariant(&"INIT"); // Debug assertion
        //self.check_only_first_two_watched(f, &"RIGHT AFTER INIT"); // Debug assertion
        return true;
    }
}