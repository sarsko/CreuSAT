use crate::{
    assignments::*, clause::*, conflict_analysis::*, decision::*, formula::*, trail::*, unit_prop::*, util::*,
    watches::*,
};


pub enum SatResult {
    Sat(Vec<AssignedState>),
    Unsat,
    Unknown,
    Err,
}

pub enum ConflictResult {
    Ok,
    Err,
    Ground,
    Continue,
}
// Satch:
/*
// fast_alpha = 0.03
  {
    struct averages *a = averages (solver);
    update_fast_average (&a->fast_glue, glue);
    update_slow_average (&a->slow_glue, glue);
    update_slow_average (&a->conflict_level, conflict_level);
    {
      const uint64_t decisions = DECISIONS;
      const uint64_t delta_decisions = decisions - a->saved_decisions;
      a->saved_decisions = decisions;
      update_slow_average (&a->decision_rate, delta_decisions);
    }
    {
      double trail_filled = percent (SIZE_STACK (solver->trail),
                     solver->statistics.remaining);
      update_slow_average (&a->trail_filled, trail_filled);
    }
    update_betas (solver);
  }

static void
update_fast_average (double *average, unsigned value)
{
  *average += fast_alpha * (value - *average);
}
*/

//&& @level < (@trail.decisions).len() //added

pub fn get_asserting_level(clause: &Clause, trail: &Trail, f: &Formula) -> (usize, u32) {
    let mut max_i: usize = 1;
    let mut max_level = trail.lit_to_level[clause.rest[1].index()];
    let mut i: usize = 2;
    while i < clause.rest.len() {
        let level = trail.lit_to_level[clause.rest[i].index()];
        if level > max_level {
            max_level = level;
            max_i = i;
        }
        i += 1;
    }
    //clause.rest.swap(1, max_i);
    return (max_i, max_level);
}

pub struct Solver {
    pub num_lemmas: usize,
    pub max_lemmas: usize,
    pub num_conflicts: usize,
    pub initial_len: usize,
    pub inc_reduce_db: usize,
    pub fast: usize,
    pub slow: usize,
    pub perm_diff: Vec<usize>,
}
/*
// MicroSat
if (S->fast > (S->slow / 100) * 125) {                        // If fast average is substantially larger than slow average
    S->res = 0; S->fast = (S->slow / 100) * 125; restart (S);   // Restart and update the averages
        if (S->nLemmas > S->maxLemmas) reduceDB (S, 6); } }
*/

impl Solver {
    pub fn new(f: &Formula) -> Solver {
        Solver {
            num_lemmas: 0,
            max_lemmas: 2000,
            num_conflicts: 0,
            initial_len: f.clauses.len(),
            inc_reduce_db: 300,
            fast: 16777216, // 1 << 24
            slow: 16777216, // 1 << 24
            perm_diff: vec![0; f.num_vars],
        }
    }

    fn increase_num_conflicts(&mut self) {
        if self.num_conflicts < usize::MAX {
            self.num_conflicts += 1;
        }
    }

    #[inline(always)]
    fn increase_num_lemmas(&mut self) {
        if self.num_lemmas < usize::MAX {
            self.num_lemmas += 1;
        }
    }

    fn handle_long_clause(
        &mut self, f: &mut Formula, t: &mut Trail, w: &mut Watches, d: &mut Decisions, clause: Clause, level: u32,
    ) {
        let cref = f.add_clause(clause, w, t);
        let mut i: usize = 0;
        let mut lbd: usize = 0;
        while i < f.clauses[cref].rest.len() {
            let level = t.lit_to_level[f.clauses[cref].rest[i].index()];
            if self.perm_diff[level as usize] != self.num_conflicts {
                self.perm_diff[level as usize] = self.num_conflicts;
                lbd += 1;
            }
            i += 1;
        }
        update_fast(&mut self.fast, lbd);
        update_slow(&mut self.slow, lbd);
        d.increment_and_move(f, cref, &t.assignments);
        // This should be removed by updating the post of get_asserting_level
        t.backtrack_safe(level, f, d);
        let lit = f.clauses[cref].rest[0];
        let step = Step { lit: lit, decision_level: level, reason: Reason::Long(cref) };
        t.enq_assignment(step, f);
        self.increase_num_lemmas();
        self.increase_num_conflicts();
    }

    fn handle_conflict(
        &mut self, f: &mut Formula, t: &mut Trail, cref: usize, w: &mut Watches, d: &mut Decisions,
    ) -> Option<bool> {
        let res = analyze_conflict(f, t, cref);
        match res {
            Conflict::Ground => {
                return Some(false);
            }
            Conflict::Unit(lit) => {
                // Okay, so the ordering here is weird. The reason for this is that the derived
                // unit clause is an equisat extension of f, but not necessarily f after reduction (even though reduction maintains equisat).
                // All of this should be looked into with regards to implementing garbage collection.
                match t.learn_unit(lit, f, d) {
                    Err(_) => return Some(true),
                    Ok(_) => {}
                }
                f.reduceDB(w, t, self);
                f.simplify_formula(w, t);
            }
            Conflict::Learned(level, mut clause) => {
                self.handle_long_clause(f, t, w, d, clause, level);
            }
            Conflict::Panic => {
                return Some(true);
            }
        }
        None
    }

    fn unit_prop_step(&mut self, f: &mut Formula, d: &mut Decisions, t: &mut Trail, w: &mut Watches) -> ConflictResult {
        return match unit_propagate(f, t, w) {
            Ok(_) => ConflictResult::Ok,
            Err(cref) => match self.handle_conflict(f, t, cref, w, d) {
                Some(false) => ConflictResult::Ground,
                Some(true) => ConflictResult::Err,
                None => ConflictResult::Continue,
            },
        };
    }

    fn unit_prop_loop(&mut self, f: &mut Formula, d: &mut Decisions, t: &mut Trail, w: &mut Watches) -> Option<bool> {
        loop {
            match self.unit_prop_step(f, d, t, w) {
                ConflictResult::Ok => {
                    return Some(true);
                }
                ConflictResult::Ground => {
                    return Some(false);
                }
                ConflictResult::Err => {
                    return None;
                }
                ConflictResult::Continue => {}
            }
        }
    }

    fn outer_loop(&mut self, f: &mut Formula, d: &mut Decisions, trail: &mut Trail, w: &mut Watches) -> SatResult {
        match self.unit_prop_loop(f, d, trail, w) {
            Some(false) => return SatResult::Unsat,
            None => return SatResult::Err,
            _ => {}
        }
        let slow = (self.slow / 100) * 125;
        if trail.decision_level() > 0 && self.fast > slow {
            self.fast = slow;
            if self.num_lemmas > self.max_lemmas {
                f.reduceDB(w, trail, self);
            }
            trail.backtrack_to(0, f, d);
        }
        match d.get_next(&trail.assignments, f) {
            Some(next) => {
                trail.enq_decision(next, f);
            }
            None => {
                return SatResult::Sat(Vec::new());
            }
        }
        SatResult::Unknown
    }

    fn inner(
        &mut self, formula: &mut Formula, mut decisions: Decisions, mut trail: Trail, mut watches: Watches,
    ) -> SatResult {
        loop {
            match self.outer_loop(formula, &mut decisions, &mut trail, &mut watches) {
                SatResult::Unknown => {} // continue
                SatResult::Sat(_) => {
                    return SatResult::Sat(trail.assignments.0);
                }
                o => {
                    return o;
                }
            }
        }
    }
}

pub fn solver(formula: &mut Formula) -> SatResult {
    match formula.check_formula_invariant() {
        SatResult::Unknown => {}
        o => return o,
    }
    let mut trail = Trail::new(formula, Assignments::new(formula));
    let mut decisions = Decisions::new(formula);
    let mut watches = Watches::new(formula);
    watches.init_watches(formula);
    match trail.learn_units(formula, &mut decisions) {
        Some(cref) => {
            return SatResult::Unsat;
        }
        None => {}
    }
    let mut solver = Solver::new(formula);
    solver.inner(formula, decisions, trail, watches)
}
