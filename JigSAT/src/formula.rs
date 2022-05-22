use crate::{assignments::*, clause::*, solver::*, trail::*, watches::*};
use std::{
    ops::{Index, IndexMut},
};
pub struct Formula {
    pub clauses: Vec<Clause>,
    pub num_vars: usize,
}

impl Index<usize> for Formula {
    type Output = Clause;
    #[inline]
    fn index(&self, i: usize) -> &Clause {
        //#[cfg(feature = "unsafe_access")]
        unsafe {
            self.clauses.get_unchecked(i)
        }
        //#[cfg(not(feature = "unsafe_access"))]
        //&self.lits[i]
    }
}

impl IndexMut<usize> for Formula {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut Clause {
        //#[cfg(feature = "unsafe_access")]
        unsafe {
            self.clauses.get_unchecked_mut(i)
        }
        //#[cfg(not(feature = "unsafe_access"))]
        //&mut self.lits[i]
    }
}

impl Formula {
    #[inline]
    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    pub fn check_formula_invariant(&self) -> SatResult {
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
        return SatResult::Unknown;
    }

    pub fn is_clause_sat(&self, idx: usize, a: &Assignments) -> bool {
        let clause = &self[idx];
        let mut i: usize = 0;
        while i < clause.len() {
            if clause[i].lit_sat(a) {
                return true;
            }
            i += 1;
        }
        return false;
    }

    pub fn swap_lits_in_clause(&mut self, trail: &Trail, watches: &Watches, cref: usize, j: usize, k: usize) {
        self[cref].rest.swap(j, k);
    }

    pub fn add_clause(&mut self, clause: Clause, watches: &mut Watches, _t: &Trail) -> usize {
        let cref = self.len();
        // The weird assignment to first_/second_lit is because otherwise we break the precond for
        // add_watcher that the cref should be less than f.len(). We can't update the watches
        // after the clause is added, as the value gets moved by the push. Could of course index on last
        // element of f after the push, but I prefer this.
        let first_lit = clause[0];
        let second_lit = clause[1];
        self.clauses.push(clause);
        watches.add_watcher(first_lit, cref, self);
        watches.add_watcher(second_lit, cref, self);
        cref
    }

    fn delete_clause(&mut self, cref: usize, watches: &mut Watches, t: &Trail) {
        watches.unwatch(self, t, cref, self[cref][0]);
        watches.unwatch(self, t, cref, self[cref][1]);
        self[cref].deleted = true;
    }

    pub fn delete_clauses(&mut self, watches: &mut Watches, t: &Trail) {
        // unwatch trivially SAT
        let mut i = 0;
        while i < self.len() {
            if !self[i].deleted {
                if self[i].len() > 1 && self.is_clause_sat(i, &t.assignments) {
                    self.delete_clause(i, watches, t);
                }
            }
            i += 1;
        }
        // TODO: Actually delete + remove UNSAT lits

        // Ideally remove UNSAT lits
    }

    pub fn simplify_formula(&mut self, watches: &mut Watches, t: &Trail) {
        // unwatch trivially SAT
        self.delete_clauses(watches, t);
        // Ideally remove UNSAT lits
    }

    pub fn reduceDB(&mut self, watches: &mut Watches, t: &Trail, s: &mut Solver) {
        s.max_len += self.len() + 300;
        let mut i = self.len() - 1;
        self.clauses[s.initial_len+1..].sort_unstable_by(|a, b| a.less_than(b));
        watches.unwatch_all_lemmas(self, s);
        let mut limit = (self.len() - s.initial_len) / 2;
        while i > s.initial_len && limit > 0 {
            self.clauses.pop();
            limit -= 1;
            i -= 1;
            /* 
            let clause = &self[i];
            if clause.lbd > 2 && clause.len() > 2 {
            } else {
                break;
            }
            */
        }
        i = s.initial_len + 1;
        while i < self.len() {
            watches.add_watcher(self[i][0], i, self);
            watches.add_watcher(self[i][1], i, self);
            i += 1;
        }
    }
}
