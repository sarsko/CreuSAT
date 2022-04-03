extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::formula::*;
use crate::lit::*;
use crate::assignments::*;
use crate::trail::*;
use crate::clause::*;


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
                @(@(@self.watches)[i])[j].cref < (@f.clauses).len() 
                /*&&
                ((@f.clauses)[@(@(@self.watches)[i])[j].cref].first.to_neg_watchidx_logic() === i ||
                (@f.clauses)[@(@(@self.watches)[i])[j].cref].second.to_neg_watchidx_logic() === i )
                */
                // Harder invariant, but might be needed

        }
    }
}

impl Watches {
    // The way clauses are made and added should really be changed - builder pattern?
    #[trusted]
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

    // This whole should be updated/merged with formula add_clause
    // We watch the negated literal for updates
    #[trusted] // OK
    #[requires(@cref < (@_f.clauses).len())]
    //#[requires((@self)[@cref].first === lit] // Should have an assertion that the watched lit is either first or second
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
    #[trusted] // OK --#[trusted] // OK-- REMOVE; USELESS FUNCTION
    #[requires(exists<j: Int> 0 <= j && j < (@(@self.watches)[old_lit.to_watchidx_logic()]).len() && 
    (@(@(@self.watches)[old_lit.to_watchidx_logic()])[j].cref) === @cref)]
    #[requires(self.invariant(*_f))]
    //#[requires(!(old_lit === new_lit))] // Strictly speaking correctness ?
    #[requires(@old_lit.idx < @usize::MAX/2)]
    #[requires(@new_lit.idx < @usize::MAX/2)]
    #[requires(old_lit.to_watchidx_logic() < (@self.watches).len())]
    #[requires(new_lit.to_neg_watchidx_logic() < (@self.watches).len())]
    #[ensures((^self).invariant(*_f))]
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
        self.move_to_end(old_idx, i, new_lit, _f);
        //let end = self.watches[old_idx].len() - 1;
        //self.watches[old_idx].swap(old_pos, end);
        match self.watches[old_idx].pop() {
            Some(w) => {
                self.watches[new_lit.to_neg_watchidx()].push(w);
            },
            None => {
                panic!("Impossible");
            }
        }
    }

    #[trusted] // OK
    #[requires(self.invariant(*_f))]
    #[requires(@new_lit.idx < @usize::MAX/2)]
    #[requires(new_lit.to_neg_watchidx_logic() < (@self.watches).len())]
    #[requires(@old_idx < (@self.watches).len())]
    #[requires(@old_pos < (@(@self.watches)[@old_idx]).len())]
    #[ensures((^self).invariant(*_f))]
    #[ensures((@(@(^self).watches)[@old_idx]).len() === ((@(@self.watches)[@old_idx]).len()))]
    pub fn move_to_end(&mut self, old_idx: usize, old_pos: usize, new_lit: Lit, _f: &Formula) {
        let end = self.watches[old_idx].len() - 1;
        self.watches[old_idx].swap(old_pos, end);
    }

    // Requires duplicates to be removed
    #[trusted] // OK
    #[requires(@f.num_vars < @usize::MAX/2)]
    #[requires(self.invariant(*f))]
    #[requires(f.invariant())]
    #[ensures((^self).invariant(*f))]
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