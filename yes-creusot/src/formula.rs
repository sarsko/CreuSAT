extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::assignments::*;
use crate::clause::*;
use crate::watches::*;


//#[derive(Debug)]
pub struct Formula {
    pub clauses: Vec<Clause>,
    pub num_vars: usize,
}

impl Formula {
    #[predicate]
    pub fn invariant(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
                (@self.clauses)[i].invariant(@self.num_vars)
        }
    }
}

impl Formula {
    /*
    #[allow(dead_code)]
    pub fn contains_empty(&self, a: &Assignments) -> bool {
        let mut i = 0;
        while i < self.clauses.len() {
            let clause = &self.clauses[i];
            if clause.is_unsat(a) {
                return true;
            }
            i += 1
        }
        return false;
    }

    */
    // TODO FIX
    #[trusted]
    #[requires(self.invariant())]
    #[ensures(watches.invariant(*self))]
    #[ensures((^self).invariant())]
    #[ensures((^watches).invariant(*self))]
    #[ensures(@(^self).num_vars === @self.num_vars)]
    pub fn add_clause(&mut self, clause: &Clause, watches: &mut Watches) -> usize {
        //self.clauses.push(clause.clone());
        let cref = self.clauses.len() - 1;
        //watches.add_watcher(clause.0[0], cref);
        //watches.add_watcher(clause.0[1], cref);
        cref
    }

    // Or people could just make correct cnfs
    // TODO add a remove_duplis for each clause as well + remove A or not A-clauses
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