use crate::{assignments::*, clause::*, solver::*, trail::*, watches::*};

pub struct Formula {
    pub clauses: Vec<Clause>,
    pub num_vars: usize,
}

//#[derive(Copy, Clone, Eq)]
pub enum SatState {
    Unknown,
    Sat,
    Unsat,
}


impl PartialEq for SatState {
    fn eq(&self, other: &Self) -> bool {
        return match (self, other) {
            (SatState::Unknown, SatState::Unknown) => true,
            (SatState::Sat, SatState::Sat) => true,
            (SatState::Unsat, SatState::Unsat) => true,
            _ => false,
        };
    }
}

impl Formula {
    pub fn check_formula_invariant(&self) -> SatResult {
        if self.num_vars >= usize::MAX / 2 {
            return SatResult::Err;
        }
        if self.clauses.len() == 0 {
            return SatResult::Sat(Vec::new());
        }
        if self.num_vars == 0 {
            return SatResult::Err; // We have no vars but more than 0 clauses -> error.
        }
        let mut i: usize = 0;
        while i < self.clauses.len() {
            if !self.clauses[i].check_clause_invariant(self.num_vars) {
                return SatResult::Err;
            }
            if self.clauses[i].len() == 0 {
                return SatResult::Unsat;
            }
            i += 1;
        }
        return SatResult::Unknown;
    }

    pub fn is_clause_sat(&self, idx: usize, a: &Assignments) -> bool {
        let clause = &self.clauses[idx];
        let mut i: usize = 0;
        while i < clause.rest.len() {
            if clause.rest[i].lit_sat(a) {
                return true;
            }
            i += 1;
        }
        return false;
    }

    pub fn swap_lits_in_clause(&mut self, trail: &Trail, watches: &Watches, cref: usize, j: usize, k: usize) {
        self.clauses[cref].rest.swap(j, k);
    }

    pub fn add_clause(&mut self, clause: Clause, watches: &mut Watches, _t: &Trail) -> usize {
        let cref = self.clauses.len();
        // The weird assignment to first_/second_lit is because otherwise we break the precond for
        // add_watcher that the cref should be less than f.clauses.len(). We can't update the watches
        // after the clause is added, as the value gets moved by the push. Could of course index on last
        // element of f.clauses after the push, but I prefer this.
        let first_lit = clause.rest[0];
        let second_lit = clause.rest[1];
        self.clauses.push(clause);
        watches.add_watcher(first_lit, cref, self);
        watches.add_watcher(second_lit, cref, self);
        cref
    }

    pub fn add_unwatched_clause(&mut self, clause: Clause, watches: &mut Watches, _t: &Trail) -> usize {
        let cref = self.clauses.len();
        self.clauses.push(clause);
        cref
    }

    pub fn make_asserting_clause_and_watch(&mut self, watches: &mut Watches, t: &Trail, idx: usize, cref: usize) {
        self.swap_lits_in_clause(t, watches, cref, 1, idx);
        let first_lit = self.clauses[cref].rest[0];
        let second_lit = self.clauses[cref].rest[1];
        watches.add_watcher(first_lit, cref, self);
        watches.add_watcher(second_lit, cref, self);
    }

    pub fn add_and_swap_first(&mut self, clause: Clause, watches: &mut Watches, t: &Trail, s_idx: usize) -> usize {
        let cref = self.add_unwatched_clause(clause, watches, t);
        self.swap_lits_in_clause(t, watches, cref, 0, s_idx);
        cref
    }

    pub fn add_unit(&mut self, clause: Clause, _t: &Trail) -> usize {
        let cref = self.clauses.len();
        self.clauses.push(clause);
        cref
    }

    pub fn is_sat(&self, a: &Assignments) -> bool {
        let mut i: usize = 0;
        while i < self.clauses.len() {
            if !self.is_clause_sat(i, a) {
                return false;
            }
            i += 1
        }
        return true;
    }

    fn delete_clause(&mut self, cref: usize, watches: &mut Watches, t: &Trail) {
        watches.unwatch(self, t, cref, self.clauses[cref].rest[0]);
        watches.unwatch(self, t, cref, self.clauses[cref].rest[1]);
        self.clauses[cref].deleted = true;
    }

    pub fn delete_clauses(&mut self, watches: &mut Watches, t: &Trail) {
        // unwatch trivially SAT
        let mut i = 0;
        while i < self.clauses.len() {
            if !self.clauses[i].deleted {
                if self.clauses[i].len() > 1 && self.is_clause_sat(i, &t.assignments) {
                    self.delete_clause(i, watches, t);
                }
            }
            i += 1;
        }

        // Ideally remove UNSAT lits
    }

    pub fn simplify_formula(&mut self, watches: &mut Watches, t: &Trail) {
        // unwatch trivially SAT
        self.delete_clauses(watches, t);
        // Ideally remove UNSAT lits
    }

    pub fn reduceDB(&mut self, watches: &mut Watches, t: &Trail, s: &mut Solver) {
        // Okay now I understand why MicroSat does this "weirdly"
        while s.num_lemmas > s.max_lemmas {
            if usize::MAX - 300 > s.max_lemmas {
                s.max_lemmas += 300;
            } else {
                break;
            }
        }
        //s.num_lemmas = 0;
        let mut i = s.initial_len;
        while i < self.clauses.len() {
            if !self.clauses[i].deleted {
                //if self.clauses[i].len() > 12 {
                if self.clauses[i].len() > 6 {
                    let mut cnt = 0;
                    let mut j = 0;
                    while j < self.clauses[i].len() && cnt < 6 {
                        if self.clauses[i].rest[j].lit_sat(&t.assignments) {
                            cnt += 1;
                        }
                        j += 1;
                    }
                    if cnt >= 6 {
                        // Maybe add the invariant that nlemmas keeps track of the number of lemmas lol
                        if s.num_lemmas > 0 {
                            s.num_lemmas -= 1;
                        }
                        self.delete_clause(i, watches, t);
                    }
                }
            }
            i += 1;
        }
    }
}
