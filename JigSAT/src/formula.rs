use crate::{assignments::*, clause::*, solver::*, solver_types::*, trail::*, watches::*};

use log::debug;
use std::ops::{Index, IndexMut};
pub struct Formula {
    pub clauses: Vec<Clause>,
    learnt_core: Vec<Cref>,
    learnt_local: Vec<Cref>,
    learnt_tier: Vec<Cref>,
    pub num_vars: usize,
    cur_restart: usize,
    num_clauses_before_reduce: usize,
    special_inc_reduce_db: usize,
    num_deleted_clauses: usize,
    next_tier_reduce: usize,
    next_local_reduce: usize,
    core_upper_bound: u32,
    tiers_upper_bound: u32,
    clause_activity_inc: f64,
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
            learnt_local: Vec::new(),
            learnt_tier: Vec::new(),
            num_vars,
            cur_restart: 1,
            num_clauses_before_reduce: 2000,
            special_inc_reduce_db: 1000,
            num_deleted_clauses: 0,
            next_tier_reduce: 10000,
            next_local_reduce: 15000,
            core_upper_bound: 3,
            tiers_upper_bound: 6,
            clause_activity_inc: 1.0,
        }
    }

    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.clauses.len()
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

    pub(crate) fn learn_clause(&mut self, mut clause: Clause, watches: &mut Watches, _t: &Trail, s: &Solver) -> Cref {
        let cref = self.len();

        self.bump_clause_activity(&mut clause);
        if clause.lbd <= self.core_upper_bound {
            self.learnt_core.push(cref);
            //c.location(ClauseLocation::core);
        } else if clause.lbd <= self.tiers_upper_bound {
            self.learnt_tier.push(cref);
            //c.location(ClauseLocation::tiers);
            clause.set_touched(s.num_conflicts as u32);
        } else {
            //c.location(ClauseLocation::local);
            self.learnt_local.push(cref);
        }

        if s.num_conflicts == 100_000 && self.learnt_core.len() < 100 {
            self.core_upper_bound = 5;
        }

        let first_lit = clause[0];
        let second_lit = clause[1];

        self.clauses.push(clause);

        watches[first_lit.to_neg_watchidx()].push(Watcher { cref, blocker: second_lit });
        watches[second_lit.to_neg_watchidx()].push(Watcher { cref, blocker: first_lit });

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
        if s.num_conflicts >= self.next_tier_reduce {
            self.next_tier_reduce += 10_000;
            self.reduce_tier_2(watches, trail, s);
        }
        if s.num_conflicts >= self.next_local_reduce {
            self.next_local_reduce += 15_000;
            self.reduce_local(watches, trail, s);
        }

        // solver.checkGarbage
    }

    #[inline]
    pub(crate) fn reduce_tier_2(&mut self, watches: &mut Watches, trail: &Trail, s: &mut Solver) {
        //self.learnt_tier.sort_unstable_by(|a, b| self.clauses[*a].less_than(&self.clauses[*b]));

        let mut i = 0;
        while i < self.learnt_tier.len() {
            let cref = self.learnt_tier[i];
            let clause = &mut self[cref];

            // Don't really get this. Is learnt_tier lazy?
            //if c.location() == ClauseLocation::Tier {

            if clause.get_touched() as usize + 30_000 < s.num_conflicts {
                //&& !trail.locked(clause[0]) {
                // Move the clause from tier to local

                clause.reset_activity();
                self.bump_cref_activity(cref);

                self.learnt_tier.swap_remove(i);
                self.learnt_local.push(cref);

                //self.unwatch_and_mark_as_deleted(cref, watches, trail);
                //c.location(ClauseLocation::local);
            } else {
                //clause.can_be_deleted = true;
                i += 1;
            }
        }
    }

    #[inline]
    pub(crate) fn reduce_local(&mut self, watches: &mut Watches, trail: &Trail, s: &mut Solver) {
        // TODO: Update less_than to check activity
        self.learnt_local.sort_unstable_by(|a, b| self.clauses[*a].less_than(&self.clauses[*b]));

        let mut limit = self.learnt_local.len() / 2;

        let mut i = 0;
        while i < self.learnt_local.len() && limit > 0 {
            let cref = self.learnt_local[i];
            let clause = &mut self[cref];

            // Don't really get this. Is learnt_local lazy?
            //if c.location() == ClauseLocation::Local {

            if clause.can_be_deleted {
                //&& !trail.locked(clause[0]) {
                self.unwatch_and_mark_as_deleted(cref, watches, trail);
                self.learnt_local.swap_remove(i);
                limit -= 1;
            } else {
                clause.can_be_deleted = true;
                i += 1;
            }
        }
    }

    /*
    // GLUCOSE STYLE
    #[inline]
    pub(crate) fn reduceDB(&mut self, watches: &mut Watches, trail: &Trail, s: &mut Solver) {
        if self.learnt_core.len() == 0 {
            return;
        }

        self.learnt_core.sort_unstable_by(|a, b| self.clauses[*a].less_than(&self.clauses[*b]));

        if self[self.learnt_core[self.learnt_core.len() / 2]].lbd <= 3 {
            self.num_clauses_before_reduce += self.special_inc_reduce_db;
        }
        if self[self.learnt_core[self.learnt_core.len() - 1]].lbd <= 5 {
            self.num_clauses_before_reduce += self.special_inc_reduce_db;
        }

        let mut limit = self.learnt_core.len() / 2;

        let mut i = 0;
        while i < self.learnt_core.len() && limit > 0 {
            let cref = self.learnt_core[i];
            let clause = &mut self[cref];
            if clause.lbd > 2 && clause.len() > 2 && clause.can_be_deleted {
                //&& !trail.locked(clause[0]) {
                self.unwatch_and_mark_as_deleted(cref, watches, trail);
                self.learnt_core.swap_remove(i);
                limit -= 1;
            } else {
                clause.can_be_deleted = true;
                i += 1;
            }
        }

    }
    */

    pub(crate) fn collect_garbage_on_empty_trail(&mut self, watches: &mut Watches, s: &Solver) {
        // If the ratio of deleted clauses to learnt clauses is less than the tresh (0.20), don't do GC
        if (self.num_deleted_clauses as f64 / self.learnt_core.len() as f64) < 0.20 {
            return;
        }

        watches.unwatch_all_lemmas(self, s);

        self.learnt_core.clear();
        self.learnt_local.clear();
        self.learnt_tier.clear();

        let mut i = s.initial_len;
        while i < self.len() {
            let clause = &self[i];
            if clause.deleted {
                self.clauses.swap_remove(i);
            } else {
                // TODO: Fix how this is done
                if clause.lbd <= self.core_upper_bound {
                    self.learnt_core.push(i);
                    //c.location(ClauseLocation::core);
                } else if clause.lbd <= self.tiers_upper_bound {
                    self.learnt_tier.push(i);
                    //c.location(ClauseLocation::tiers);
                    //clause.set_touched(s.num_conflicts as u32);
                } else {
                    //c.location(ClauseLocation::local);
                    self.learnt_local.push(i);
                }
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

    // TODO
    pub(crate) fn update_clause(&mut self, cref: Cref) {}

    pub(crate) fn bump_clause_activity(&mut self, clause: &mut Clause) {
        if clause.bump_activity(self.clause_activity_inc as f32) > 1e20 {
            // Rescale
            for e in &self.learnt_core {
                self.clauses[*e].activity *= 1e-20;
            }
            self.clause_activity_inc *= 1e-20;
        }
    }

    pub(crate) fn bump_cref_activity(&mut self, cref: Cref) {
        let clause = &mut self.clauses[cref];
        if clause.bump_activity(self.clause_activity_inc as f32) > 1e20 {
            // Rescale
            for e in &self.learnt_core {
                self.clauses[*e].activity *= 1e-20;
            }
            self.clause_activity_inc *= 1e-20;
        }
    }
}
