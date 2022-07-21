use crate::{
    assignments::*, clause::*, conflict_analysis::*, decision::*, formula::*, lit::*, modes::*, preprocess::*,
    restart::*, target_phase::*, trail::*, unit_prop::*, util::*, watches::*,
};

use log::debug;

pub enum SatResult {
    Sat(Vec<AssignedState>),
    Unsat,
    Unknown,
    Err,
}

pub(crate) enum ConflictResult {
    Ok,
    Ground,
    Continue,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SearchMode {
    //Target,
    Stable,
    Focus,
    OnlyStable,
    OnlyFocus,
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

#[derive(Debug, Default)]
pub(crate) struct Stats {
    pub(crate) num_glues: usize,
    pub(crate) num_binary: usize,
    pub(crate) num_unary: usize,
    pub(crate) lcm_tested: usize,
    pub(crate) lcm_reduced: usize,
    pub(crate) nb_walk: usize,
    pub(crate) walk_time: usize,
    pub(crate) nb_flips: usize,
    pub(crate) no_decision_conflict: usize,
    pub(crate) nb_reduced_clauses: usize,
    pub(crate) nb_self_subsumptions: usize,
    pub(crate) nb_stats: usize,
}

pub(crate) struct Solver {
    pub(crate) num_conflicts: usize,
    pub(crate) num_decisions: usize,
    pub(crate) initial_len: usize,
    pub(crate) perm_diff: Vec<usize>,
    pub(crate) analyze_stack: Vec<Lit>,
    pub(crate) analyze_toclear: Vec<Lit>,
    pub(crate) stats: Stats,
    pub(crate) search_mode: SearchMode,
    pub(crate) restart: Restart,
    pub(crate) next_phase_change: usize,
    pub(crate) ticks: usize,
    pub(crate) num_phase_changes: usize,
    pub(crate) a_decision_was_made: bool,
    pub(crate) adapt_strategies: bool,
    //pub seen: Vec<bool>,
}
/*
// MicroSat
if (S->fast > (S->slow / 100) * 125) {                        // If fast average is substantially larger than slow average
    S->res = 0; S->fast = (S->slow / 100) * 125; restart (S);   // Restart and update the averages
        if (S->nLemmas > S->maxLemmas) reduceDB (S, 6); } }
*/

impl Solver {
    fn new(f: &Formula) -> Solver {
        Solver {
            //max_len: f.len() + 2000,
            num_conflicts: 0,
            num_decisions: 0,
            initial_len: f.len(),
            //inc_reduce_db: 300,
            //special_inc_reduce_db: 1000,
            perm_diff: vec![0; f.num_vars],
            analyze_stack: Vec::new(),
            analyze_toclear: Vec::new(),
            //seen: vec![false; f.num_vars],
            stats: Stats::default(),
            search_mode: SearchMode::Focus,
            restart: Restart::new(),
            next_phase_change: 1023,
            ticks: 0,
            num_phase_changes: 1,
            a_decision_was_made: false,
            adapt_strategies: true,
        }
    }

    #[inline]
    fn handle_long_clause(
        &mut self, formula: &mut Formula, trail: &mut Trail, watches: &mut Watches, decisions: &mut impl Decisions,
        clause: Clause, level: u32, target_phase: &mut TargetPhase,
    ) {
        let clause_len = clause.len();
        let lbd = clause.lbd;
        let cref = formula.learn_clause(clause, watches, trail, self);

        self.restart.glucose.update(trail.trail.len(), lbd as usize);
        self.restart.block_restart(self.num_conflicts);

        if lbd == 2 {
            self.stats.num_glues += 1;
        }
        if clause_len == 2 {
            self.stats.num_binary += 1;
        }

        //d.increment_and_move(f, cref, &t.assignments);
        trail.backtrack_to(level, formula, decisions, target_phase);
        let lit = formula[cref][0];
        trail.enq_assignment(lit, formula, cref);
    }

    #[inline]
    fn handle_conflict(
        &mut self, formula: &mut Formula, trail: &mut Trail, cref: usize, watches: &mut Watches,
        decisions: &mut impl Decisions, target_phase: &mut TargetPhase,
    ) -> bool {
        let res = analyze_conflict(formula, trail, cref, decisions, self);
        match res {
            Conflict::Ground => {
                return false;
            }
            Conflict::Unit(lit) => {
                self.restart.glucose.update(trail.trail.len(), 1);
                self.restart.block_restart(self.num_conflicts);
                self.stats.num_unary += 1;

                trail.learn_unit(lit, formula, decisions, watches, self, target_phase);
                formula.reduceDB(watches, trail, self);
            }
            Conflict::Learned(level, clause) => {
                self.handle_long_clause(formula, trail, watches, decisions, clause, level, target_phase);
            }
        }

        decisions.decay_var_inc();
        //claDecayActivity();

        if self.adapt_strategies && self.num_conflicts == 100000 && adapt_solver(self, decisions) {
            trail.restart(formula, decisions, watches, self, target_phase);
        }

        true
    }

    #[inline]
    fn unit_prop_step(
        &mut self, formula: &mut Formula, decisions: &mut impl Decisions, trail: &mut Trail, watches: &mut Watches,
        target_phase: &mut TargetPhase,
    ) -> ConflictResult {
        match unit_propagate(formula, trail, watches, &mut self.ticks) {
            Ok(_) => ConflictResult::Ok,
            Err(cref) => {
                self.num_conflicts += 1;

                if !self.a_decision_was_made {
                    self.stats.no_decision_conflict += 1;
                }
                self.a_decision_was_made = false;

                if self.search_mode == SearchMode::Stable || self.search_mode == SearchMode::OnlyStable {
                    target_phase.update_best_phase(trail);
                }

                match self.handle_conflict(formula, trail, cref, watches, decisions, target_phase) {
                    true => ConflictResult::Continue,
                    false => ConflictResult::Ground,
                }
            }
        }
    }

    #[inline]
    fn unit_prop_loop(
        &mut self, formula: &mut Formula, decisions: &mut impl Decisions, trail: &mut Trail, watches: &mut Watches,
        target_phase: &mut TargetPhase,
    ) -> bool {
        loop {
            match self.unit_prop_step(formula, decisions, trail, watches, target_phase) {
                ConflictResult::Ok => {
                    return true;
                }
                ConflictResult::Ground => {
                    return false;
                }
                ConflictResult::Continue => {}
            }
        }
    }

    #[inline]
    fn outer_loop(
        &mut self, formula: &mut Formula, decisions: &mut impl Decisions, trail: &mut Trail, watches: &mut Watches,
        target_phase: &mut TargetPhase,
    ) -> SatResult {
        match self.unit_prop_loop(formula, decisions, trail, watches, target_phase) {
            true => {}
            false => return SatResult::Unsat,
        }
        if self.restart.trigger_restart(self.num_conflicts) {
            trail.restart(formula, decisions, watches, self, target_phase);
            return SatResult::Unknown;
        }
        if (self.search_mode == SearchMode::Stable || self.search_mode == SearchMode::OnlyStable)
            && target_phase.should_rephase(self.num_conflicts)
        {
            if target_phase.rephase(self.num_conflicts) {
                println!("c Solved by local search engine");
                return SatResult::Sat(Vec::new()); // TODO: Get satisfying assignment
            }
        }
        if trail.decision_level() == 0 && !self.simplify(formula, decisions, trail, watches) {
            return SatResult::Unsat;
        }

        if formula.trigger_reduce(self.num_conflicts, self.initial_len) {
            formula.reduceDB(watches, trail, self);
        }

        match decisions.get_next(&trail.assignments, formula) {
            Some(next) => {
                self.num_decisions += 1;
                self.a_decision_was_made = true;
                trail.enq_decision(next, formula, target_phase, self.search_mode == SearchMode::Focus);
            }
            None => {
                debug!("SAT: no more decisions");
                return SatResult::Sat(Vec::new());
            }
        }

        if (self.search_mode == SearchMode::Focus || self.search_mode == SearchMode::Stable)
            && self.ticks > self.next_phase_change
        {
            change_mode(self, decisions, target_phase);
        }

        SatResult::Unknown
    }

    #[inline]
    fn solve(
        mut self, mut formula: Formula, mut decisions: impl Decisions, mut trail: Trail, mut watches: Watches,
        mut target_phase: TargetPhase,
    ) -> SatResult {
        loop {
            match self.outer_loop(&mut formula, &mut decisions, &mut trail, &mut watches, &mut target_phase) {
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

    fn simplify(
        &mut self, formula: &mut Formula, decisions: &mut impl Decisions, trail: &mut Trail, watches: &mut Watches,
    ) -> bool {
        // TODO: Add subsumption here.
        formula.simplify_formula(watches, trail);
        return true;
    }
}

pub fn solver(mut formula: Formula) -> SatResult {
    let mut trail = Trail::new(&formula, Assignments::new(&formula));

    match trail.learn_units(&mut formula) {
        Some(_) => {
            println!("c UNSAT due to learn_units");
            return SatResult::Unsat;
        }
        None => {}
    }

    let mut watches = Watches::new(&formula);
    watches.init_watches(&formula);

    let mut decisions: VSIDS = Decisions::new(&formula);

    if !Preprocess::new().preprocess(&mut formula, &mut trail, &mut decisions, &mut watches) {
        println!("c UNSAT by preprocess");
        return SatResult::Unsat;
    }
    debug!("done with preproc");
    debug!("{:?}", &trail.trail);

    let target_phase = TargetPhase::new(formula.num_vars);
    let solver = Solver::new(&formula);

    solver.solve(formula, decisions, trail, watches, target_phase)
}
