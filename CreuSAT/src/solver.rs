use ::std::panic;

use creusot_contracts::{std::*, Snapshot, *};

use crate::{
    assignments::*, clause::*, conflict_analysis::*, decision::*, formula::*, trail::*, unit_prop::*, util::*,
    watches::*,
};

// Tmp
#[cfg(creusot)]
use crate::logic::{logic::*, logic_clause::*, logic_formula::*};

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

#[cfg_attr(feature = "trust_solver", trusted)]
#[requires(f.inv())]
#[requires(trail.inv(*f))]
#[requires(equisat_extension_inner(*clause, f@))]
#[requires(clause.inv(f.num_vars@))]
#[requires(clause@.len() > 1)]
#[requires(vars_in_range_inner(clause@, f.num_vars@))]
#[requires(no_duplicate_indexes_inner(clause@))]
#[ensures(result.0@ < clause@.len())]
pub fn get_asserting_level(clause: &Clause, trail: &Trail, f: &Formula) -> (usize, usize) {
    let mut max_i: usize = 1;
    let mut max_level = trail.lit_to_level[clause[1].index()];
    let mut i: usize = 2;
    #[invariant(max_i@ < clause@.len())]
    while i < clause.len() {
        let level = trail.lit_to_level[clause[i].index()];
        if level > max_level {
            max_level = level;
            max_i = i;
        }
        i += 1;
    }
    //clause.rest.swap(1, max_i);
    (max_i, max_level)
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
    #[cfg_attr(feature = "trust_solver", trusted)]
    pub fn new(f: &Formula) -> Solver {
        Solver {
            num_lemmas: 0,
            max_lemmas: 2000,
            num_conflicts: 0,
            initial_len: f.clauses.len(),
            inc_reduce_db: 300,
            fast: 16777216, // 1 << 24
            slow: 16777216, // 1 << 24
            perm_diff: vec::from_elem(0, f.num_vars),
        }
    }

    #[cfg_attr(feature = "trust_solver", trusted)]
    #[inline(always)]
    fn increase_num_conflicts(&mut self) {
        if self.num_conflicts < usize::MAX {
            self.num_conflicts += 1;
        }
    }

    #[cfg_attr(feature = "trust_solver", trusted)]
    #[inline(always)]
    fn increase_num_lemmas(&mut self) {
        if self.num_lemmas < usize::MAX {
            self.num_lemmas += 1;
        }
    }

    #[cfg_attr(feature = "trust_solver", trusted)]
    #[maintains((mut f).inv())]
    #[maintains((mut t).inv(mut f))]
    #[maintains((mut w).inv(mut f))]
    #[maintains((mut d).inv(f.num_vars@))]
    #[requires(f.num_vars@ < usize::MAX@/2)]
    #[requires(clause.inv(f.num_vars@))]
    #[requires(equisat_extension_inner(clause, f@))]
    #[requires((clause@).len() > 1)]
    #[requires(s_idx@ < (clause@).len())]
    #[ensures(f.num_vars@ == (^f).num_vars@)]
    #[ensures(f.equisat(^f))]
    fn handle_long_clause(
        &mut self, f: &mut Formula, t: &mut Trail, w: &mut Watches, d: &mut Decisions, mut clause: Clause, s_idx: usize,
    ) {
        clause.swap_lits_in_clause(f, s_idx, 0);
        let (idx, level) = get_asserting_level(&clause, t, f);
        clause.swap_lits_in_clause(f, idx, 1);

        // TODO: Store lbd in clause
        let lbd = clause.calc_lbd(f, self, t);
        let cref = f.add_clause(clause, w, t);
        update_fast(&mut self.fast, lbd);
        update_slow(&mut self.slow, lbd);

        // TODO: Remove by updating the post of get_asserting_level
        t.backtrack_safe(level, f, d);

        let lit = f[cref][0];
        let step = Step { lit: lit, decision_level: level, reason: Reason::Long(cref) };

        // TODO:
        // These two have to be ensured by analysis + backtrack
        //proof_assert!(f.clauses@[cref@].unit(t.assignments));
        //proof_assert!(unset((@t.assignments)[@step.lit.idx]));
        if f[cref].unit_and_unset(&t.assignments, f) {
            t.enq_assignment(step, f);
        }

        self.increase_num_lemmas();
        self.increase_num_conflicts();
    }

    #[cfg_attr(feature = "trust_solver", trusted)]
    #[maintains((mut f).inv())]
    #[maintains((mut t).inv(mut f))]
    #[maintains((mut w).inv(mut f))]
    #[maintains((mut d).inv(f.num_vars@))]
    #[requires(f.num_vars@ < usize::MAX@/2)]
    #[requires(cref@ < f.clauses@.len())]
    #[requires(f.clauses@[cref@].unsat(t.assignments))]
    #[ensures(f.num_vars@ == (^f).num_vars@)]
    #[ensures(f.equisat(^f))]
    /*
    // TODO: https://github.com/creusot-rs/creusot/issues/1504
    #[ensures(match result {
        Some(false) => { (^f).not_satisfiable() },
        Some(true)  => { true },
        None        => { true },
    })]
    */
    #[ensures(match result {
        Some(b) => { if b { true } else { (^f).not_satisfiable() }},
        None        => { true },
    })]
    fn handle_conflict(
        &mut self, f: &mut Formula, t: &mut Trail, cref: usize, w: &mut Watches, d: &mut Decisions,
    ) -> Option<bool> {
        let res = analyze_conflict(f, t, cref, d);
        match res {
            Conflict::Ground => {
                return Some(false);
            }
            Conflict::Unit(clause) => {
                // Okay, so the ordering here is weird. The reason for this is that the derived
                // unit clause is an equisat extension of f, but not necessarily f after reduction (even though reduction maintains equisat).
                // All of this should be looked into with regards to implementing garbage collection.
                let cref = f.add_unit(clause, t);
                match t.learn_unit(cref, f, d) {
                    Err(_) => return Some(true),
                    Ok(_) => {}
                }

                f.reduceDB(w, t, self);
                f.simplify_formula(w, t);
            }
            Conflict::Learned(s_idx, mut clause) => {
                self.handle_long_clause(f, t, w, d, clause, s_idx);
            }
            Conflict::Restart(clause) => {
                f.add_clause(clause, w, t);
                t.backtrack_safe(0, f, d);
            }
        }
        None
    }

    #[cfg_attr(feature = "trust_solver", trusted)]
    #[maintains((mut f).inv())]
    #[maintains((mut w).inv(mut f))]
    #[maintains((mut t).inv(mut f))]
    #[maintains((mut d).inv(f.num_vars@))]
    #[requires(f.num_vars@ < usize::MAX@/2)]
    #[ensures(f.num_vars@ == (^f).num_vars@)]
    #[ensures(f.equisat(^f))]
    #[ensures(match result {
        ConflictResult::Ground => { (^f).not_satisfiable() },
        _                      => { true }
    })]
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

    #[cfg_attr(feature = "trust_solver", trusted)]
    #[maintains((mut f).inv())]
    #[maintains((mut t).inv(mut f))]
    #[maintains((mut w).inv(mut f))]
    #[maintains((mut d).inv(f.num_vars@))]
    #[requires(f.num_vars@ < usize::MAX@/2)]
    // TODO: https://github.com/creusot-rs/creusot/issues/1504
    /*
    #[ensures(match result {
        Some(false) => { (^f).not_satisfiable() },
        Some(true)  => { true },
        None        => { true },
    })]
    */
    #[ensures(match result {
        Some(b) => if b { true } else { (^f).not_satisfiable() },
        None        => { true },
    })]
    #[ensures(f.num_vars@ == (^f).num_vars@)]
    #[ensures(f.equisat(^f))]
    fn unit_prop_loop(&mut self, f: &mut Formula, d: &mut Decisions, t: &mut Trail, w: &mut Watches) -> Option<bool> {
        let old_f: Snapshot<&mut Formula> = snapshot! { f };
        let old_t: Snapshot<&mut Trail> = snapshot! { t };
        let old_w: Snapshot<&mut Watches> = snapshot! { w };
        let old_d: Snapshot<&mut Decisions> = snapshot! { d };
        #[invariant(f.inv())]
        #[invariant(t.inv(*f))]
        #[invariant(w.inv(*f))]
        #[invariant(d.inv(f.num_vars@))]
        #[invariant(old_f.inner().equisat(*f))]
        #[invariant(f.num_vars@ == old_f.num_vars@)]
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

    #[cfg_attr(feature = "trust_solver", trusted)]
    #[maintains((mut f).inv())]
    #[maintains((mut trail).inv(mut f))]
    #[maintains((mut w).inv(mut f))]
    #[maintains((mut d).inv(f.num_vars@))]
    #[requires(d.inv(f.num_vars@))]
    #[requires(f.num_vars@ < usize::MAX@/2)]
    #[ensures(f.num_vars@ == (^f).num_vars@)]
    #[ensures(f.equisat(^f))]
    #[ensures(match result {
        SatResult::Sat(_)   => { (^f).sat((^trail).assignments)
                            &&   ((^trail).assignments).complete() }, // Do I really need this for anything?
        SatResult::Unsat    => { (^f).not_satisfiable() },
        SatResult::Unknown  => { true }
        SatResult::Err      => { true }
    })]
    fn outer_loop(&mut self, f: &mut Formula, d: &mut Decisions, trail: &mut Trail, w: &mut Watches) -> SatResult {
        match self.unit_prop_loop(f, d, trail, w) {
            Some(false) => return SatResult::Unsat,
            None => return SatResult::Err,
            _ => {}
        }
        let slow = if self.slow < usize::MAX / 2 { (self.slow / 100) * 125 } else { self.slow };
        if trail.decision_level() > 0 && self.fast > slow {
            self.fast = slow;
            if self.num_lemmas > self.max_lemmas {
                f.reduceDB(w, trail, self);
            }
            trail.backtrack_to(0, f, d);
        }
        //proof_assert!(!a.complete() || !f.unsat(*a)); // Need to get from unit_prop_loop
        match d.get_next(&trail.assignments, f) {
            Some(next) => {
                trail.enq_decision(next, f);
            }
            None => {
                // This is gonna get broken if one changes the definition of unsat
                // Okay so this got broken from unit prop not returning full eval anymore.
                // Seems like we either have to become ternary and do a check(which cannot fail)
                // or do a rather long proof about the correctness of watched literals
                if f.is_sat(&trail.assignments) {
                    return SatResult::Sat(Vec::new());
                } else {
                    return SatResult::Err; // This should never happen
                }
            }
        }
        SatResult::Unknown
    }

    // OK
    #[cfg_attr(feature = "trust_solver", trusted)]
    #[requires(formula.num_vars@ < usize::MAX@/2)]
    #[requires(formula.inv())]
    #[requires(decisions.inv(formula.num_vars@))]
    #[requires(trail.inv(*formula))]
    #[requires(watches.inv(*formula))]
    #[requires(decisions.inv(formula.num_vars@))]
    #[ensures(match result {
        SatResult::Sat(v) => { (^formula).sat_inner(v@) && formula.equisat(^formula) && formula.eventually_sat_complete() },
        SatResult::Unsat => { (^formula).not_satisfiable() && formula.equisat(^formula) }
        _ => true,
    })]
    #[ensures(formula.equisat(^formula))]
    fn inner(
        &mut self, formula: &mut Formula, mut decisions: Decisions, mut trail: Trail, mut watches: Watches,
    ) -> SatResult {
        let old_f: Snapshot<&mut Formula> = snapshot! { formula };
        #[invariant(old_f.inner().equisat(*formula))]
        #[invariant(formula.num_vars@ == old_f.num_vars@)]
        #[invariant(formula.inv())]
        #[invariant(trail.inv(*formula))]
        #[invariant(watches.inv(*formula))]
        #[invariant(decisions.inv(formula.num_vars@))]
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

#[cfg_attr(feature = "trust_solver", trusted)]
#[ensures(match result {
    SatResult::Sat(assn) => { formula_sat_inner((^formula)@, assn@) && formula.equisat(^formula) },
    SatResult::Unsat     => { (^formula).not_satisfiable() && formula.equisat(^formula) },
    _                    => { true },
})]
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
        None => {}
        Some(true) => return SatResult::Unsat,
        Some(false) => return SatResult::Err,
    }
    let mut solver = Solver::new(formula);
    solver.inner(formula, decisions, trail, watches)
}
