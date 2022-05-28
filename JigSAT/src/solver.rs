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


pub struct Solver {
    pub max_len: usize,
    pub num_conflicts: usize,
    pub initial_len: usize,
    pub inc_reduce_db: usize,
    pub special_inc_reduce_db: usize,
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
            max_len: f.len() + 2000,
            num_conflicts: 0,
            initial_len: f.len(),
            inc_reduce_db: 300,
            special_inc_reduce_db: 1000,
            fast: 16777216, // 1 << 24
            slow: 16777216, // 1 << 24
            perm_diff: vec![0; f.num_vars],
        }
    }

    #[inline]
    fn increase_num_conflicts(&mut self) {
        //if self.num_conflicts < usize::MAX {
            self.num_conflicts += 1;
        //}
    }


    #[inline]
    fn handle_long_clause(
        &mut self, f: &mut Formula, t: &mut Trail, w: &mut Watches, d: &mut Decisions, clause: Clause, level: u32,
    ) {
        self.increase_num_conflicts();
        //clause.calc_and_set_lbd(t, self);
        let lbd = clause.lbd;
        let cref = f.add_clause(clause, w, t);
        update_fast(&mut self.fast, lbd as usize);
        update_slow(&mut self.slow, lbd as usize);
        //d.increment_and_move(f, cref, &t.assignments);
        t.backtrack_to(level, f, d);
        let lit = f[cref][0];
        let step = Step { lit, decision_level: level, reason: Reason::Long(cref) };
        t.enq_assignment(step, f);
    }

    #[inline]
    fn handle_conflict(
        &mut self, f: &mut Formula, t: &mut Trail, cref: usize, w: &mut Watches, d: &mut Decisions,
    ) -> Option<bool> {
        let res = analyze_conflict(f, t, cref, d);
        match res {
            Conflict::Ground => {
                return Some(false);
            }
            Conflict::Unit(lit) => {
                t.learn_unit(lit, f, d);
                f.reduceDB(w, t, self);
                f.simplify_formula(w, t);
            }
            Conflict::Learned(level, clause) => {
                self.handle_long_clause(f, t, w, d, clause, level);
            }
        }
        None
    }

    #[inline]
    fn unit_prop_step(&mut self, f: &mut Formula, d: &mut Decisions, t: &mut Trail, w: &mut Watches) -> ConflictResult {
        match unit_propagate(f, t, w) {
            Ok(_) => ConflictResult::Ok,
            Err(cref) => match self.handle_conflict(f, t, cref, w, d) {
                Some(false) => ConflictResult::Ground,
                Some(true) => ConflictResult::Err,
                None => ConflictResult::Continue,
            },
        }
    }

    #[inline]
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

    #[inline]
    fn outer_loop(&mut self, f: &mut Formula, d: &mut Decisions, trail: &mut Trail, w: &mut Watches) -> SatResult {
        let old_len = f.len();
        match self.unit_prop_loop(f, d, trail, w) {
            Some(false) => return SatResult::Unsat,
            None => return SatResult::Err,
            _ => {}
        }
        if f.len() > old_len {

        let slow = (self.slow / 100) * 125;
        if self.fast > slow {
            self.fast = slow;
            trail.backtrack_safe(0, f, d);
            if f.len() > self.max_len {
                f.reduceDB(w, trail, self);
            }
        }
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

    #[inline]
    fn inner(
        &mut self, mut formula: Formula, mut decisions: Decisions, mut trail: Trail, mut watches: Watches,
    ) -> SatResult {
        loop {
            match self.outer_loop(&mut formula, &mut decisions, &mut trail, &mut watches) {
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

pub fn solver(mut formula: Formula) -> SatResult {
    match formula.check_formula_invariant() {
        SatResult::Unknown => {}
        o => return o,
    }
    let mut trail = Trail::new(&formula, Assignments::new(&formula));
    match trail.learn_units(&mut formula) {
        Some(_) => {
            return SatResult::Unsat;
        }
        None => {}
    }
    if formula.len() == 0 {
        return SatResult::Sat(Vec::new());
    }
    let decisions = Decisions::new(&formula);
    let mut watches = Watches::new(&formula);
    watches.init_watches(&formula);
    let mut solver = Solver::new(&formula);
    solver.inner(formula, decisions, trail, watches)
}
