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

#[predicate]
fn watches_invariant_internal2(w: Seq<Vec<Watcher>>, n: Int, f: Formula) -> bool {
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
                @(@(@self.watches)[i])[j].cref < (@f.clauses).len() &&
                (@(@f.clauses)[@(@(@self.watches)[i])[j].cref]).len() > 1
        }
    }
}

impl Watches {
    // The way clauses are made and added should really be changed - builder pattern?
    #[trusted] // Checks out
    #[ensures(result.invariant(*f))]
    pub fn new(f: &Formula) -> Watches {
        let mut i: usize = 0;
        let mut watches = Vec::new();
        #[invariant(i_less, @i <= @f.num_vars)]
        #[invariant(maintains_inv, watches_invariant_internal2(@watches, @i, *f))]
        while i < f.num_vars {
            watches.push(Vec::new());
            watches.push(Vec::new());
            i += 1;
        }
        Watches { watches }
    }

    // We watch the negated literal for updates
    #[trusted] // Checks out
    #[requires(@cref < (@_f.clauses).len())]
    #[requires((@(@_f.clauses)[@cref]).len() > 1)] // really unsure of whether this should be in formula or in watcher
    #[requires(self.invariant(*_f))]
    #[ensures((^self).invariant(*_f))]
    #[requires(@lit.idx < @usize::MAX/2)]
    #[requires(lit.to_neg_watchidx_logic() < (@self.watches).len())]
    #[ensures((@self.watches).len() === (@(^self).watches).len())]
    pub fn add_watcher(&mut self, lit: Lit, cref: usize, _f: &Formula) {
        self.watches[lit.to_neg_watchidx()].push(Watcher { cref });
    }

    // This requires the literal to be watched, otherwise it will panic
    // This method should be updated as we usually know where to look
    #[trusted] // Checks out
    #[requires(exists<j: Int> 0 <= j && j < (@(@self.watches)[old_lit.to_watchidx_logic()]).len() && 
    (@(@(@self.watches)[old_lit.to_watchidx_logic()])[j].cref) === @cref)]
    #[requires(self.invariant(*_f))]
    #[ensures((^self).invariant(*_f))]
    //#[requires(!(old_lit === new_lit))] // Strictly speaking correctness ?
    #[requires(@old_lit.idx < @usize::MAX/2)]
    #[requires(@new_lit.idx < @usize::MAX/2)]
    #[requires(old_lit.to_watchidx_logic() < (@self.watches).len())]
    #[requires(new_lit.to_neg_watchidx_logic() < (@self.watches).len())]
    pub fn update_watch(&mut self, old_lit: Lit, new_lit: Lit, cref: usize, _f: &Formula) {
        //assert!(old_lit != new_lit);
        let mut i: usize = 0;
        let old_idx = old_lit.to_watchidx();
        proof_assert!((*self).invariant(*_f));
        #[invariant(i_less, @i <= (@(@self.watches)[@old_idx]).len())]
        #[invariant(not_found, forall<j: Int> 0 <= j && j < @i ==>
            !((@(@(@self.watches)[@old_idx])[j].cref) === @cref))]
        while i < self.watches[old_idx].len() {
            if self.watches[old_idx][i].cref == cref {
                break;
            }
            i += 1;
        }
        //assert!(self.watches[old_idx][i].cref == cref);
        //self.check_invariant("UPDATE_BEFORE");

        // Both of these are better than the swap + pop
        //let old = self.watches[old_idx].remove(i);
        //let old = self.watches[old_idx].swap_remove(i);

        // Workaround for remove.

        // Okay so I for some reason had to to it like this to make the proof pass
        // I'll look at undoing it later, but it may be useful when proving correctness
        self.remove(old_idx, i, new_lit, _f);
        match self.watches[old_idx].pop() {
            Some(w) => {
                //proof_assert!(@w.cref < (@_f.clauses).len());
                //proof_assert!((@(@_f.clauses)[@w.cref]).len() > 1);
                self.watches[new_lit.to_neg_watchidx()].push(w);
            },
            None => {
                panic!("Impossible");
            }
        }

        //self.check_invariant("UPDATE_AFTER");
    }

    #[trusted] // Checks out
    #[requires(self.invariant(*_f))]
    #[requires(@new_lit.idx < @usize::MAX/2)]
    #[requires(new_lit.to_neg_watchidx_logic() < (@self.watches).len())]
    #[requires(@old_idx < (@self.watches).len())]
    #[requires(@old_pos < (@(@self.watches)[@old_idx]).len())]
    #[ensures((^self).invariant(*_f))]
    #[ensures((@(@(^self).watches)[@old_idx]).len() === ((@(@self.watches)[@old_idx]).len()))]
    fn remove(&mut self, old_idx: usize, old_pos: usize, new_lit: Lit, _f: &Formula) {
        let end = self.watches[old_idx].len() - 1;
        self.watches[old_idx].swap(old_pos, end);
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
    #[trusted] // Checks out
    #[requires(@f.num_vars < @usize::MAX/2)]
    #[requires(self.invariant(*f))]
    #[requires(f.invariant())]
    #[requires(a.invariant(@f.num_vars))]
    #[requires(trail.invariant(@f.num_vars))]
    #[requires((@trail.trail).len() === 1)]
    #[ensures((^trail).invariant(@f.num_vars))]
    #[ensures((^self).invariant(*f))]
    #[ensures((^a).invariant(@f.num_vars))]
    #[ensures((@self.watches).len() === (@(^self).watches).len())]
    #[ensures((@(^trail).trail).len() === 1)]
    pub fn init_watches(&mut self, f: &Formula, trail: &mut Trail, a: &mut Assignments) -> bool {
        let mut i = 0;
        let old_self = Ghost::record(&self);
        let old_a = Ghost::record(&a);
        let old_trail = Ghost::record(&trail);
        #[invariant(same_len, (@(*self).watches).len() === (@(*@old_self).watches).len())]
        #[invariant(maintains_invariant, self.invariant(*f))]
        #[invariant(intact, ^self === ^@old_self)]
        #[invariant(intact2, ^a === ^@old_a)]
        #[invariant(intact3, ^trail === ^@old_trail)]
        #[invariant(trail_len, (@trail.trail).len() === 1)]
        #[invariant(maintains_ass_inv, a.invariant(@f.num_vars))]
        #[invariant(maintains_trail_inv, trail.invariant(@f.num_vars))]
        while i < f.clauses.len() {
            let clause = &f.clauses[i].0;
            if clause.len() == 0 {
                return false;
            } else if clause.len() == 1 {
                match a.0[clause[0].idx]{
                    Some(_) => { return false; },
                    None => { 
                        learn_unit(a, trail, clause[0], f);
                    }
                }
            } else {
                let mut j = 0;
                #[invariant(maintains_invariant, self.invariant(*f))]
                #[invariant(same_len, (@(*self).watches).len() === (@(*@old_self).watches).len())]
                #[invariant(intact, ^self === ^@old_self)]
                while j < 2 {
                    let lit = clause[j];
                    self.add_watcher(lit, i, f);
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