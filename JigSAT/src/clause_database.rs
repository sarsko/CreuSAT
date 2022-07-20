use crate::{
    clause::*,
    lit::*,
    solver::*,
    solver_types::{Cref, SatResult},
    trail::*,
    watches::*,
};

use log::debug;
use std::ops::{Index, IndexMut};

pub struct ClauseArena {
    arena: Vec<Lit>,
    num_vars: usize,
    learnt_core: Vec<Cref>,
}

// LITS BEFORE THE FIRST LITERAL OF THE CLAUSE
const HEADER_LEN: usize = 2;
/*
pub(crate) trait ClauseDB {
    fn new(num_vars: usize) -> Self;

    fn len(&self) -> usize;

    //fn index(&self, i: usize) -> &Clause;

    //fn index_mut(&mut self, i: usize) -> &mut Clause;

    fn check_invariant(&self) -> SatResult;

    //sfn learn_clause(&mut self, clause: Clause, watches: &mut Watches, _t: &Trail) -> Cref;

    fn add_unwatched_clause(&mut self, clause: Clause) -> usize;

    fn remove_clause_in_preprocessing(&mut self, cref: usize);

    fn mark_clause_as_deleted(&mut self, cref: usize);

    fn remove_deleted(&mut self);

    fn delete_clauses(&mut self, watches: &mut Watches, t: &Trail);

    fn simplify_db_on_empty_trail(&mut self, watches: &mut Watches, t: &Trail);

    fn reduce_db(&mut self, watches: &mut Watches, trail: &Trail, s: &mut Solver);

    fn collect_garbage_on_empty_trail(&mut self, watches: &mut Watches, s: &Solver);

    fn mark_clauses_as_deleted(&mut self, crefs: &mut Vec<Cref>);

    fn trigger_reduce(&mut self, num_conflicts: usize, initial_len: usize) -> bool;

    //fn iter(&self) -> impl Iterator<Item=&Clause> + '_;

    fn num_vars(&self) -> usize;
}
*/

// For all of these: cref HAS TO point to a valid clause header
impl ClauseArena {
    pub(crate) fn new() -> Self {
        ClauseArena { arena: Vec::new(), num_vars: 0, learnt_core: Vec::new() }
    }

    pub(crate) fn add_unwatched_clause(&mut self, clause: Vec<Lit>) {
        //let cref = self.len();

        for l in Clause::create_header(&clause) {
            self.arena.push(l);
        }

        for l in clause {
            if l.index() >= self.num_vars {
                self.num_vars = l.index() + 1;
            }
            self.arena.push(l);
        }

        //cref
    }

    pub(crate) fn get_literals(&self, cref: Cref) -> &[Lit] {
        let header = self.arena[cref + 1].get_len_from_header_lit();
        let out = &self.arena[cref + HEADER_LEN..cref + HEADER_LEN + header as usize];
        assert!(out.len() == header as usize);

        out
    }

    pub(crate) fn get_literals_mut(&mut self, cref: Cref) -> &mut [Lit] {
        unimplemented!()
    }

    pub(crate) fn get_lbd(&self, cref: Cref) -> u32 {
        unimplemented!()
    }

    pub(crate) fn get_first_literal(&self, cref: Cref) -> Lit {
        // Cref is header, cref + 1 is len, cref + 2 is first lit
        self.arena[cref + 2]
    }

    pub(crate) fn get_second_literal(&self, cref: Cref) -> Lit {
        self.arena[cref + 3]
    }

    pub(crate) fn swap(&mut self, cref: Cref, i: usize, j: usize) {
        self.arena.swap(cref + HEADER_LEN + i, cref + HEADER_LEN + j);
    }
}

impl ClauseArena {
    // len != num_clauses
    #[inline(always)]
    pub(crate) fn len(&self) -> usize {
        self.arena.len()
        //unimplemented!();
        //self.clauses.len()
    }

    #[inline(always)]
    pub(crate) fn num_vars(&self) -> usize {
        self.num_vars
        //unimplemented!();
        //self.num_vars
    }

    /*
    fn check_invariant(&self) -> SatResult {
        unimplemented!();
    }
    */

    pub(crate) fn learn_clause(&mut self, clause: Vec<Lit>, watches: &mut Watches, _t: &Trail) -> Cref {
        let cref = self.len();

        for l in Clause::create_header(&clause) {
            self.arena.push(l);
        }

        let first_lit = clause[0];
        let second_lit = clause[1];

        for l in clause {
            self.arena.push(l);
        }

        watches[first_lit.to_neg_watchidx()].push(Watcher { cref, blocker: second_lit });
        watches[second_lit.to_neg_watchidx()].push(Watcher { cref, blocker: first_lit });
        self.learnt_core.push(cref);

        cref
    }

    /*
    // This is only valid to run before solver is created and before watches are added.
    fn remove_clause_in_preprocessing(&mut self, cref: usize) {
        unimplemented!();
    }

    #[inline(always)]
    fn mark_clause_as_deleted(&mut self, cref: usize) {
        unimplemented!();
    }

    fn remove_deleted(&mut self) {
        unimplemented!();
    }
    */

    fn delete_clauses(&mut self, watches: &mut Watches, t: &Trail) {
        unimplemented!();
    }

    // Has to be called on an empty trail.
    fn simplify_db_on_empty_trail(&mut self, watches: &mut Watches, t: &Trail) {
        unimplemented!();
    }

    #[inline]
    fn reduce_db(&mut self, watches: &mut Watches, trail: &Trail, s: &mut Solver) {
        unimplemented!();
    }

    fn collect_garbage_on_empty_trail(&mut self, watches: &mut Watches, s: &Solver) {
        /*
        // If the ratio of deleted clauses to learnt clauses is less than the tresh (0.20), don't do GC
        if (self.num_deleted_clauses as f64 / self.learnt_core.len() as f64) < 0.20 {
            return;
        }
        */
        unimplemented!();
    }

    fn mark_clauses_as_deleted(&mut self, crefs: &mut Vec<Cref>) {
        unimplemented!();
        /*
        debug!("Marking {:?} as deleted", crefs);
        crefs.sort();
        crefs.reverse();
        for cref in crefs {
            self.mark_clause_as_deleted(*cref);
        }
        */
    }

    fn trigger_reduce(&mut self, num_conflicts: usize, initial_len: usize) -> bool {
        /*
        if num_conflicts >= (self.cur_restart * self.num_clauses_before_reduce) && self.len() > initial_len {
            self.cur_restart = (num_conflicts / self.num_clauses_before_reduce) + 1;
            return true;
        }
        */
        false
    }
}
