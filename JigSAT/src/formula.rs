use crate::{assignments::*, clause::*, lit::*, solver::*, solver_types::*, trail::*, watches::*};

use log::debug;
use std::ops::{Index, IndexMut};
pub struct Formula {
    pub clauses: Vec<Clause>,
    learnt_core: Vec<Cref>,
    pub num_vars: usize,
    cur_restart: usize,
    num_clauses_before_reduce: usize,
    special_inc_reduce_db: usize,
    num_deleted_clauses: usize,
}

impl Index<usize> for Formula {
    type Output = Clause;
    #[inline]
    fn index(&self, i: usize) -> &Clause {
        //#[cfg(feature = "unsafe_access")]
        unsafe { self.clauses.get_unchecked(i) }
        //#[cfg(not(feature = "unsafe_access"))]
        //&self.lits[i]
    }
}

impl IndexMut<usize> for Formula {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut Clause {
        //#[cfg(feature = "unsafe_access")]
        unsafe { self.clauses.get_unchecked_mut(i) }
        //#[cfg(not(feature = "unsafe_access"))]
        //&mut self.lits[i]
    }
}

impl Formula {
    pub fn new(num_vars: usize) -> Formula {
        Formula {
            clauses: Vec::new(),
            learnt_core: Vec::new(),
            num_vars,
            cur_restart: 1,
            num_clauses_before_reduce: 2000,
            special_inc_reduce_db: 1000,
            num_deleted_clauses: 0,
        }
    }

    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.clauses.len()
    }

    pub(crate) fn check_formula_invariant(&self) -> SatResult {
        if self.num_vars >= usize::MAX / 2 {
            return SatResult::Err;
        }
        if self.len() == 0 {
            return SatResult::Sat(Vec::new());
        }
        if self.num_vars == 0 {
            return SatResult::Err; // We have no vars but more than 0 clauses -> error.
        }
        let mut i: usize = 0;
        while i < self.len() {
            if !self[i].check_clause_invariant(self.num_vars) {
                return SatResult::Err;
            }
            if self[i].len() == 0 {
                return SatResult::Unsat;
            }
            i += 1;
        }
        SatResult::Unknown
    }

    pub(crate) fn is_clause_sat(&self, idx: usize, a: &Assignments) -> bool {
        let clause = &self[idx];
        let mut i: usize = 0;
        while i < clause.len() {
            if clause[i].lit_sat(a) {
                return true;
            }
            i += 1;
        }
        false
    }

    pub(crate) fn swap_lits_in_clause(&mut self, trail: &Trail, watches: &Watches, cref: usize, j: usize, k: usize) {
        self[cref].swap(j, k);
    }

    pub(crate) fn learn_clause(&mut self, clause: Clause, watches: &mut Watches, _t: &Trail) -> Cref {
        let cref = self.len();
        // The weird assignment to first_/second_lit is because otherwise we break the precond for
        // add_watcher that the cref should be less than f.len(). We can't update the watches
        // after the clause is added, as the value gets moved by the push. Could of course index on last
        // element of f after the push, but I prefer this.
        let first_lit = clause[0];
        let second_lit = clause[1];
        self.clauses.push(clause);
        watches[first_lit.to_neg_watchidx()].push(Watcher { cref, blocker: second_lit });
        watches[second_lit.to_neg_watchidx()].push(Watcher { cref, blocker: first_lit });
        self.learnt_core.push(cref);
        cref
    }

    pub(crate) fn add_unwatched_clause(&mut self, clause: Clause) -> usize {
        let cref = self.len();
        self.clauses.push(clause);
        cref
    }

    // This is only valid to run before solver is created and before watches are added.
    pub(crate) fn remove_clause_in_preprocessing(&mut self, cref: usize) {
        //self.clauses[cref].deleted = true;
        self.clauses.swap_remove(cref);
    }

    #[inline(always)]
    pub(crate) fn mark_clause_as_deleted(&mut self, cref: usize) {
        self.clauses[cref].deleted = true;
        self.num_deleted_clauses += 1;
        //self.clauses.remove(cref);
    }

    pub(crate) fn remove_deleted(&mut self) {
        let mut i = 0;
        while i < self.len() {
            if self[i].deleted {
                self.clauses.swap_remove(i);
            } else {
                i += 1;
            }
        }
        self.num_deleted_clauses = 0;
    }

    #[inline(always)]
    fn unwatch_and_mark_as_deleted(&mut self, cref: usize, watches: &mut Watches, t: &Trail) {
        watches.unwatch(self, t, cref, self[cref][0]);
        watches.unwatch(self, t, cref, self[cref][1]);
        self.mark_clause_as_deleted(cref);
    }

    pub(crate) fn delete_clauses(&mut self, watches: &mut Watches, t: &Trail) {
        // unwatch trivially SAT
        let mut i = 0;
        while i < self.len() {
            if !self[i].deleted {
                if self[i].len() > 1 && self.is_clause_sat(i, &t.assignments) {
                    self.unwatch_and_mark_as_deleted(i, watches, t);
                }
            }
            i += 1;
        }

        // Ideally remove UNSAT lits
    }

    // Has to be called on an empty trail.
    pub(crate) fn simplify_formula(&mut self, watches: &mut Watches, t: &Trail) {
        // unwatch trivially SAT
        self.delete_clauses(watches, t);
        // Ideally remove UNSAT lits
    }

    #[inline]
    pub(crate) fn reduceDB(&mut self, watches: &mut Watches, trail: &Trail, s: &mut Solver) {
        if self.learnt_core.len() == 0 {
            return;
        }
        self.learnt_core.sort_unstable_by(|a, b| self.clauses[*a].less_than(&self.clauses[*b]));
        //s.max_len += self.len() + 300;
        //self.num_reduced += 1;
        if self[self.learnt_core[self.learnt_core.len() / 2]].lbd <= 3 {
            self.num_clauses_before_reduce += self.special_inc_reduce_db;
        }
        if self[self.learnt_core[self.learnt_core.len() - 1]].lbd <= 5 {
            self.num_clauses_before_reduce += self.special_inc_reduce_db;
        }
        //watches.unwatch_all_lemmas(self, s);
        let mut limit = self.learnt_core.len() / 2;

        let mut i = 0;
        while i < self.learnt_core.len() && limit > 0 {
            let cref = self.learnt_core[i];
            let clause = &mut self[cref];
            if clause.lbd > 2 && clause.len() > 2 && clause.can_be_deleted { //&& !trail.locked(clause[0]) {
                self.unwatch_and_mark_as_deleted(cref, watches, trail);
                self.learnt_core.swap_remove(i);
                limit -= 1;
            } else {
                clause.can_be_deleted = true;
                i += 1;
            }
        }

        /*
        if self.time_for_garbage_collection() {
            self.collect_garbage();
        }
        */
        /*
        i = s.initial_len;
        while i < self.len() {
            watches[self[i][0].to_neg_watchidx()].push(Watcher { cref: i, blocker: self[i][1] });
            watches[self[i][1].to_neg_watchidx()].push(Watcher { cref: i, blocker: self[i][0] });
            i += 1;
        }
        */
    }

    pub(crate) fn collect_garbage_on_empty_trail(&mut self, watches: &mut Watches, s: &Solver) {
        // If the ratio of deleted clauses to learnt clauses is less than the tresh (0.20), don't do GC
        if (self.num_deleted_clauses as f64 / self.learnt_core.len() as f64) < 0.20 {
            return;
        }

        watches.unwatch_all_lemmas(self, s);

        self.learnt_core.clear();
        let mut i = s.initial_len;
        while i < self.len() {
            if self[i].deleted {
                self.clauses.swap_remove(i);
            } else {
                self.learnt_core.push(i);
                i += 1;
            }
        }

        let mut i = s.initial_len;
        while i < self.len() {
            watches[self[i][0].to_neg_watchidx()].push(Watcher { cref: i, blocker: self[i][1] });
            watches[self[i][1].to_neg_watchidx()].push(Watcher { cref: i, blocker: self[i][0] });
            i += 1;
        }
    }

    pub(crate) fn mark_clauses_as_deleted(&mut self, crefs: &mut Vec<Cref>) {
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
