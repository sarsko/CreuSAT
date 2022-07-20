use crate::{
    clause::*,
    lit::*,
    solver::*,
    solver_types::{Cref, SatResult},
    trail::*,
    watches::*,
};

use std::{
    cmp::Ordering,
    ops::{Index, IndexMut},
};

use log::debug;

pub struct ClauseArena {
    arena: Vec<Lit>,
    num_vars: usize,
    initial_len: usize,
    learnt_core: Vec<Cref>,
    cur_restart: usize,
    num_clauses_before_reduce: usize,
    special_inc_reduce_db: usize,
    num_deleted_clauses: usize,
}

// WARNING! THIS BREAKS ABSTRACTION BARRIERS
fn less_than(left: &[Lit], right: &[Lit]) -> Ordering {
    if left[1].get_len_from_header_lit() == 2 {
        if right[1].get_len_from_header_lit() == 2 {
            Ordering::Equal
        } else {
            Ordering::Less
        }
    } else if right[1].get_len_from_header_lit() == 2 {
        Ordering::Greater
    } else if left[1].get_lbd() < right[0].get_lbd() {
        Ordering::Less
    } else if left[0].get_lbd() > right[0].get_lbd() {
        Ordering::Greater
    } else if left[1].get_len_from_header_lit() < right[1].get_len_from_header_lit() {
        Ordering::Less
    } else if left[1].get_len_from_header_lit() > right[1].get_len_from_header_lit() {
        Ordering::Greater
    } else {
        Ordering::Equal
    }
}

// LITS BEFORE THE FIRST LITERAL OF THE CLAUSE
const HEADER_LEN: usize = 2;

// For all of these: cref HAS TO point to a valid clause header
impl ClauseArena {
    pub(crate) fn new() -> Self {
        ClauseArena {
            arena: Vec::new(),
            num_vars: 0,
            initial_len: 0,
            learnt_core: Vec::new(),
            cur_restart: 1,
            num_clauses_before_reduce: 2000,
            special_inc_reduce_db: 1000,
            num_deleted_clauses: 0,
        }
    }

    pub(crate) fn add_initial_clause(&mut self, clause: Vec<Lit>) {
        //let cref = self.len();

        for l in Clause::create_header(&clause, 0) {
            self.arena.push(l);
        }

        for l in clause {
            if l.index() >= self.num_vars {
                self.num_vars = l.index() + 1;
            }
            self.arena.push(l);
        }

        self.initial_len = self.len();

        //cref
    }

    pub(crate) fn get_literals(&self, cref: Cref) -> &[Lit] {
        let header = self.arena[cref + 1].get_len_from_header_lit();
        let out = &self.arena[cref + HEADER_LEN..cref + HEADER_LEN + header as usize];

        out
    }

    pub(crate) fn get_literals_mut(&mut self, cref: Cref) -> &mut [Lit] {
        unimplemented!()
    }

    pub(crate) fn get_lbd(&self, cref: Cref) -> u32 {
        self.arena[cref].get_lbd()
    }

    pub(crate) fn get_first_literal(&self, cref: Cref) -> Lit {
        // Cref is header, cref + 1 is len, cref + 2 is first lit
        //self.arena[cref + 2]
        unsafe { *self.arena.get_unchecked(cref + 2) }
    }

    pub(crate) fn get_second_literal(&self, cref: Cref) -> Lit {
        //self.arena[cref + 3]
        unsafe { *self.arena.get_unchecked(cref + 3) }
    }

    pub(crate) fn swap(&mut self, cref: Cref, i: usize, j: usize) {
        self.arena.swap(cref + HEADER_LEN + i, cref + HEADER_LEN + j);
    }

    pub(crate) fn is_deleted(&self, cref: Cref) -> bool {
        self.arena[cref].to_be_deleted()
    }

    pub(crate) fn can_be_deleted(&self, cref: Cref) -> bool {
        self.arena[cref].can_be_deleted()
    }

    // len != num_clauses
    #[inline(always)]
    pub(crate) fn len(&self) -> usize {
        self.arena.len()
    }

    #[inline(always)]
    pub(crate) fn num_vars(&self) -> usize {
        self.num_vars
    }

    pub(crate) fn learn_clause(&mut self, clause: Vec<Lit>, watches: &mut Watches, _t: &Trail, lbd: u32) -> Cref {
        let cref = self.len();

        for l in Clause::create_header(&clause, lbd) {
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

    // This is only valid to run before solver is created and before watches are added.
    fn remove_clause_in_preprocessing(&mut self, cref: usize) {
        unimplemented!();
    }

    #[inline(always)]
    fn get_len(&mut self, cref: Cref) -> u32 {
        self.arena[cref + 1].get_len_from_header_lit()
    }

    #[inline(always)]
    fn mark_clause_as_deleted(&mut self, cref: Cref) {
        self.arena[cref].set_deleted()
    }

    fn remove_deleted(&mut self) {
        unimplemented!();
    }

    fn delete_clauses(&mut self, watches: &mut Watches, t: &Trail) {
        unimplemented!();
    }

    // Has to be called on an empty trail.
    pub(crate) fn simplify_db_on_empty_trail(&mut self, watches: &mut Watches, t: &Trail) {
        unimplemented!();
    }

    #[inline]
    pub(crate) fn reduce_db(&mut self, watches: &mut Watches, trail: &Trail, s: &mut Solver) {
        if self.learnt_core.len() < 1000 {
            return;
        }
        self.learnt_core.sort_unstable_by(|a, b| less_than(&self.arena[*a..*a + 2], &self.arena[*b..*b + 2]));
        //s.max_len += self.len() + 300;
        //self.num_reduced += 1;
        if self.arena[self.learnt_core[self.learnt_core.len() / 2]].get_lbd() <= 3 {
            self.num_clauses_before_reduce += self.special_inc_reduce_db;
        }
        if self.arena[self.learnt_core[self.learnt_core.len() - 1]].get_lbd() <= 5 {
            self.num_clauses_before_reduce += self.special_inc_reduce_db;
        }
        //watches.unwatch_all_lemmas(self, s);
        let mut limit = self.learnt_core.len() / 2;

        let mut i = 0;
        while i < self.learnt_core.len() && limit > 0 {
            let cref = self.learnt_core[i];
            if self.get_lbd(cref) > 2 && self.get_len(cref) > 2 && self.can_be_deleted(cref) {
                //&& !trail.locked(clause[0]) {
                self.unwatch_and_mark_as_deleted(cref, watches, trail);
                self.learnt_core.swap_remove(i);
                limit -= 1;
            } else {
                self.mark_clause_as_deleted(cref);
                i += 1;
            }
        }
    }

    #[inline(always)]
    fn unwatch_and_mark_as_deleted(&mut self, cref: usize, watches: &mut Watches, t: &Trail) {
        watches.unwatch(self, t, cref, self.get_first_literal(cref));
        watches.unwatch(self, t, cref, self.get_second_literal(cref));
        self.mark_clause_as_deleted(cref);
    }

    pub(crate) fn collect_garbage_on_empty_trail(&mut self, watches: &mut Watches, s: &Solver) {
        // If the ratio of deleted clauses to learnt clauses is less than the tresh (0.20), don't do GC
        if (self.num_deleted_clauses as f64 / self.learnt_core.len() as f64) < 0.20 {
            return;
        }

        watches.unwatch_all_lemmas(self, s);

        self.learnt_core.clear();

        let mut i = self.initial_len;
        let mut j = self.initial_len;
        while i < self.len() {
            let total_len = HEADER_LEN + self.get_len(i) as usize;
            if self.is_deleted(i) {
                i += total_len;
            } else {
                self.learnt_core.push(j);
                let mut k = j;
                j += total_len;
                while k < j {
                    self.arena[k] = self.arena[i];
                    k += 1;
                    j += 1;
                }
                //i += total_len;
            }
        }

        self.arena.truncate(j);

        for cref in &self.learnt_core {
            let first_lit = self.get_first_literal(*cref);
            let second_lit = self.get_second_literal(*cref);
            watches[first_lit.to_neg_watchidx()].push(Watcher { cref: *cref, blocker: second_lit });
            watches[second_lit.to_neg_watchidx()].push(Watcher { cref: *cref, blocker: first_lit });
        }
    }

    fn mark_clauses_as_deleted(&mut self, crefs: &mut Vec<Cref>) {
        debug!("Marking {:?} as deleted", crefs);
        crefs.sort();
        crefs.reverse();
        for cref in crefs {
            self.mark_clause_as_deleted(*cref);
        }
    }

    pub(crate) fn trigger_reduce(&mut self, num_conflicts: usize, initial_len: usize) -> bool {
        if num_conflicts >= (self.cur_restart * self.num_clauses_before_reduce) && self.len() > initial_len {
            self.cur_restart = (num_conflicts / self.num_clauses_before_reduce) + 1;
            return true;
        }

        false
    }
}
