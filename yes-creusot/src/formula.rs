extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;

//use crate::assignments::*;
use crate::clause::*;
use crate::watches::*;
use crate::lit::*;


//#[derive(Debug)]
pub struct Formula {
    pub clauses: Vec<Clause>,
    pub num_vars: usize,
}

/*
#[logic]
#[requires(c.vars_in_range(n))]
#[ensures(c.idxs_in_range(2*n))]
pub fn lemma_vars_in_range_implies_watchidx_in_range(c: Clause, n: Int) {}
*/

#[logic]
#[requires(f.vars_in_range())]
#[ensures(f.idxs_in_range())]
pub fn lemma_vars_in_range_implies_watchidx_in_range_formula(f: Formula) {}


impl Formula {
    #[predicate]
    pub fn invariant(self) -> bool {
        pearlite! {
            @self.num_vars > 0 && // Added, watch out
            forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
                (@self.clauses)[i].invariant(self)
        }
    }

    #[predicate]
    pub fn vars_in_range(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
                (@self.clauses)[i].vars_in_range(@self.num_vars)
        }
    }

    #[predicate]
    pub fn idxs_in_range(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
                (@self.clauses)[i].idxs_in_range(2 * @self.num_vars)
        }
    }
}

impl Formula {
    #[trusted] // OK
    #[requires((@self.clauses).len() > 0)]
    #[requires(@self.num_vars < @usize::MAX/2)]
    #[requires(self.invariant())]
    #[requires(watches.invariant(*self))]
    #[requires(invariant(@clause, *self))]
    #[requires(forall<i: Int> 0 <= i && i < (@clause).len() ==>
                @((@clause)[i]).idx < @self.num_vars &&
                (((@clause)[i])).to_neg_watchidx_logic() < (@watches.watches).len()
            )]
    #[requires((@clause).len() > 1)]
    #[ensures((^self).invariant())] // TODO
    #[ensures((^watches).invariant(^self))]
    #[ensures(@(^self).num_vars === @self.num_vars)]
    #[ensures((@(^self).clauses).len() === (@self.clauses).len() + 1)]
    #[ensures(@result === (@(^self).clauses).len() - 1)] // new
    #[ensures((@watches.watches).len() === (@(^watches).watches).len())]
    pub fn add_clause(&mut self, clause: &Vec<Lit>, watches: &mut Watches) -> usize {
        let clause = Clause::clause_from_vec(clause, self);   
        let first = clause.first;
        let second = clause.second;
        let cref = self.clauses.len();
        self.clauses.push(clause);
        //watches.watches[first.to_neg_watchidx()].push(Watcher { cref });
        //watches.watches[second.to_neg_watchidx()].push(Watcher { cref });
        watches.add_watcher(first, cref, self);
        watches.add_watcher(second, cref, self);
        cref
    }

    #[trusted] // OK
    /*
    #[requires((@self.clauses).len() > 0)]
    #[requires(@self.num_vars < @usize::MAX/2)]
    #[requires(self.invariant())]
    #[requires(watches.invariant(*self))]
    #[requires(invariant(@clause, *self))]
    #[requires(forall<i: Int> 0 <= i && i < (@clause).len() ==>
                @((@clause)[i]).idx < @self.num_vars &&
                (((@clause)[i])).to_neg_watchidx_logic() < (@watches.watches).len()
            )]
    #[requires((@clause).len() > 1)]
    */
    #[ensures((^self).invariant())] // TODO
    #[ensures((^watches).invariant(^self))]
    #[ensures(@(^self).num_vars === @self.num_vars)]
    #[ensures((@(^self).clauses).len() === (@self.clauses).len() + 1)]
    #[ensures(@result === (@(^self).clauses).len() - 1)] // new
    #[ensures((@watches.watches).len() === (@(^watches).watches).len())]
    pub fn mock_add_clause(&mut self, clause: &Vec<Lit>, watches: &mut Watches) -> usize {
        let clause = Clause::clause_from_vec(clause, self);   
        let first = clause.first;
        let second = clause.second;
        let cref = self.clauses.len();
        self.clauses.push(clause);
        //watches.watches[first.to_neg_watchidx()].push(Watcher { cref });
        //watches.watches[second.to_neg_watchidx()].push(Watcher { cref });
        watches.add_watcher(first, cref, self);
        watches.add_watcher(second, cref, self);
        cref
    }

    // Or people could just make correct cnfs
    // TODO add a remove_duplis for each clause as well + remove A or not A-clauses
    // TODO FIX
    #[trusted]
    #[requires(self.invariant())]
    #[ensures((^self).invariant())]
    #[ensures(@(^self).num_vars === @self.num_vars)]
    pub fn remove_duplicates(&mut self) {
        panic!()
        /*
        use std::collections::HashSet;
        let mut uniques = HashSet::new();
        self.clauses.retain(|e| uniques.insert(e.clone()));
        */
    }
}