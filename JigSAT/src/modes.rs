// An attempt to separate out the modes and phases stuff

use crate::{decision::*, restart::*, solver::*, target_phase::TargetPhase};

//#[inline(always)]
pub(crate) fn adapt_solver(solver: &mut Solver, decisions: &mut impl Decisions) -> bool {
    solver.adapt_strategies = false;
    let dec_to_confl_ratio = (solver.num_decisions as f64) / (solver.num_conflicts as f64);
    if dec_to_confl_ratio <= 1.2 {
        println!("c Adjusting for low decision levels");
        solver.restart.set_restart_mode(RestartMode::Glucose);
        solver.search_mode = SearchMode::OnlyFocus;
        // (If one adds tiered clause management: set core_upper_bound to 5 in formula.)
        return true;
    }

    if solver.stats.no_decision_conflict < 30000 {
        println!("c Adjusting for low successive conflicts");
        solver.restart.set_restart_mode(RestartMode::Luby);
        solver.search_mode = SearchMode::OnlyStable; // OnlyFocus in Glucose
        decisions.set_var_decay(0.999);
        return true;
    }
    false
}

//#[inline(always)]
pub(crate) fn change_mode(solver: &mut Solver, decisions: &mut impl Decisions, target_phase: &mut TargetPhase) {
    solver.next_phase_change = solver.ticks + solver.num_phase_changes * 15_000_000;
    solver.num_phase_changes += 1;
    match solver.search_mode {
        SearchMode::Stable => {
            println!("c Changing mode to Focus mode");
            solver.restart.swap_mode();
            decisions.set_var_decay(0.95);
            solver.search_mode = SearchMode::Focus;
        }
        SearchMode::Focus => {
            println!("c Changing mode to Stable mode");
            solver.restart.swap_mode();
            decisions.set_var_decay(0.75);
            solver.search_mode = SearchMode::Stable;
            target_phase.reset();
        }
        _ => {}
    }
}
