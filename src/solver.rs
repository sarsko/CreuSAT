extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{
    assignments::*, clause::*, conflict_analysis::*, decision::*, formula::*, lit::*,
    trail::*, unit_prop::*, watches::*,
};

// Tmp
#[cfg(feature = "contracts")]
use crate::logic::{logic::*, logic_formula::*};

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

pub struct Solver {
    pub nLemmas: usize,
    pub maxLemmas: usize,
    pub nConflicts: usize,
    pub initialLen: usize,
    pub incReduceDb: usize,
}
/*
if (S->fast > (S->slow / 100) * 125) {                        // If fast average is substantially larger than slow average
    //        printf("c restarting after %i conflicts (%i %i) %i\n", S->res, S->fast, S->slow, S->nLemmas > S->maxLemmas);
            S->res = 0; S->fast = (S->slow / 100) * 125; restart (S);   // Restart and update the averages
            if (S->nLemmas > S->maxLemmas) reduceDB (S, 6); } }
            */

impl Solver {
    pub fn new(f: &Formula) -> Solver {
        Solver {
            nLemmas: 0,
            maxLemmas: 2000,
            nConflicts: 0,
            initialLen: f.clauses.len(),
            incReduceDb: 300,
        }
    }

    #[cfg_attr(feature = "trust_solver", trusted)]
    #[maintains((mut f).invariant())]
    #[maintains((mut t).invariant(mut f))]
    #[maintains((mut w).invariant(mut f))]
    #[maintains((mut d).invariant(@f.num_vars))]
    #[requires(@f.num_vars < @usize::MAX/2)]
    #[requires(@cref < (@f.clauses).len())]
    #[requires((@f.clauses)[@cref].unsat(t.assignments))] // added
    #[ensures(@f.num_vars === @(^f).num_vars)]
    #[ensures(f.equisat(^f))]
    #[ensures(match result {
        Some(false) => { (^f).not_satisfiable() },
        Some(true)  => { true },
        None        => { true },
    })]
    fn handle_conflict(&mut self, f: &mut Formula, t: &mut Trail, cref: usize, w: &mut Watches, d: &mut Decisions) -> Option<bool> {
        let res = analyze_conflict(f, t, cref);
        match res {
            Conflict::Ground => {
                return Some(false);
            }
            Conflict::Unit(clause) => {
                // Have to do a proof that it isnt already unit?
                let cref = f.add_unit(clause, t);
                match t.learn_unit(cref, f, d) {
                    Err(_) => return Some(true),
                    Ok(_)  => {},
                }
                //f.simplify_formula(w, t, self);
                //f.reduceDB(w, t, self);
            }
            Conflict::Learned(level, clause) => {
                let lit = clause.rest[0];
                let cref = f.add_clause(clause, w, t);
                d.increment_and_move(f, cref, &t.assignments);
                t.backtrack_to(level, f, d);
                let step = Step {
                    lit: lit,
                    decision_level: level,
                    reason: Reason::Long(cref),
                };
                t.enq_assignment(step, f);
                /*
                self.nConflicts += 1;
                self.nLemmas += 1;
                if self.nLemmas > self.maxLemmas {
                    f.reduceDB(w, t, self);
                }
                */
            }
            Conflict::Panic => { return Some(true); }
        }
        None
    }

    // OK
    #[cfg_attr(feature = "trust_solver", trusted)]
    #[maintains((mut f).invariant())]
    #[maintains((mut w).invariant(mut f))]
    #[maintains((mut t).invariant(mut f))]
    #[maintains((mut d).invariant(@f.num_vars))]
    #[requires(@f.num_vars < @usize::MAX/2)]
    #[requires(d.invariant(@f.num_vars))] // d is here because it will later become mutable and updated in handle_conflict
    #[ensures(@f.num_vars === @(^f).num_vars)]
    #[ensures(f.equisat(^f))]
    #[ensures(match result {
        ConflictResult::Ground => { (^f).not_satisfiable() },
        _                      => { true }
    })]
    fn unit_prop_step(
        &mut self,
        f: &mut Formula,
        d: &mut Decisions,
        t: &mut Trail,
        w: &mut Watches,
    ) -> ConflictResult {
        return match unit_propagate(f, t, w) {
            Ok(_)     => ConflictResult::Ok,
            Err(cref) => match self.handle_conflict(f, t, cref, w, d) {
                Some(false) => ConflictResult::Ground,
                Some(true)  => ConflictResult::Err,
                None        => ConflictResult::Continue,
            },
        };
    }

    // OK
    #[cfg_attr(feature = "trust_solver", trusted)]
    #[maintains((mut f).invariant())]
    #[maintains((mut t).invariant(mut f))]
    #[maintains((mut w).invariant(mut f))]
    #[maintains((mut d).invariant(@f.num_vars))]
    #[requires(@f.num_vars < @usize::MAX/2)]
    #[ensures(match result {
        Some(false) => { (^f).not_satisfiable() },
        Some(true)  => { true },
        None        => { true },
    })]
    #[ensures(@f.num_vars === @(^f).num_vars)]
    #[ensures(f.equisat(^f))]
    fn unit_prop_loop(&mut self, f: &mut Formula, d: &mut Decisions, t: &mut Trail, w: &mut Watches) -> Option<bool> {
        let old_f = Ghost::record(&f);
        let old_t = Ghost::record(&t);
        let old_w = Ghost::record(&w);
        let old_d = Ghost::record(&d);
        #[invariant(maintains_f, f.invariant())]
        #[invariant(maintains_t, t.invariant(*f))]
        #[invariant(maintains_w, w.invariant(*f))]
        #[invariant(maintains_d, d.invariant(@f.num_vars))]
        #[invariant(equi, (@old_f).equisat(*f))]
        #[invariant(num_vars, @f.num_vars === @(@old_f).num_vars)]
        #[invariant(prophf, ^f === ^@old_f)]
        #[invariant(propht, ^t === ^@old_t)]
        #[invariant(prophw, ^w === ^@old_w)]
        #[invariant(prophd, ^d === ^@old_d)]
        loop {
            match self.unit_prop_step(f, d, t, w) {
                ConflictResult::Ok       => { return Some(true); },
                ConflictResult::Ground   => { return Some(false); },
                ConflictResult::Err      => { return None; },
                ConflictResult::Continue => {},
            }
        }
    }

    // OK
    #[cfg_attr(feature = "trust_solver", trusted)]
    #[maintains((mut f).invariant())]
    #[maintains((mut trail).invariant(mut f))]
    #[maintains((mut w).invariant(mut f))]
    #[maintains((mut d).invariant(@f.num_vars))]
    #[requires(d.invariant(@f.num_vars))]
    #[requires(@f.num_vars < @usize::MAX/2)]
    #[ensures(@f.num_vars === @(^f).num_vars)]
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
            None        => return SatResult::Err,
            _           => {}
        }
        //proof_assert!(!a.complete() || !f.unsat(*a)); // Need to get from unit_prop_loop
        match d.get_next(&trail.assignments, f) {
        //match trail.assignments.find_unassigned(d, f) {
            Some(next) => {
                //trail.enq_decision(lit, f);
                trail.enq_decision(next, f);
                //t.assignments.0[next] -= 2;
            }
            None => {
                // This is gonna get broken if one changes the definition of unsat
                // Okay so this got broken from unit prop not returning full eval anymore.
                // Seems like we either have to become ternary and do a check(which cannot fail)
                // or do a rather long proof about the correctness of watched literals
                //proof_assert!(a.complete());
                //proof_assert!(!f.unsat(*a));
                //proof_assert!(lemma_complete_and_not_unsat_implies_sat(*f, @a); true);
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
    #[requires(@formula.num_vars < @usize::MAX/2)]
    #[requires(formula.invariant())]
    #[requires(decisions.invariant(@formula.num_vars))]
    #[requires(trail.invariant(*formula))]
    #[requires(watches.invariant(*formula))]
    #[requires(decisions.invariant(@formula.num_vars))]
    #[ensures(match result {
        SatResult::Sat(v) => { (^formula).sat_inner(@v) && formula.equisat(^formula) && formula.eventually_sat_complete_no_ass()},
        SatResult::Unsat => { (^formula).not_satisfiable() && formula.equisat(^formula) }
        _ => true,
    })]
    #[ensures(formula.equisat(^formula))]
    fn inner(
        &mut self, 
        formula: &mut Formula,
        mut decisions: Decisions,
        mut trail: Trail,
        mut watches: Watches,
    ) -> SatResult {
        let old_f = Ghost::record(&formula);
        #[invariant(equi, (@old_f).equisat(*formula))]
        #[invariant(num_vars, @formula.num_vars === @(@old_f).num_vars)]
        #[invariant(maintains_f, formula.invariant())]
        #[invariant(maintains_t, trail.invariant(*formula))]
        #[invariant(maintains_w, watches.invariant(*formula))]
        #[invariant(maintains_d, decisions.invariant(@formula.num_vars))]
        #[invariant(prophf, ^formula === ^@old_f)]
        loop {
            match self.outer_loop(formula, &mut decisions, &mut trail, &mut watches) {
                SatResult::Unknown => {}, // continue
                SatResult::Sat(_)  => { return SatResult::Sat(trail.assignments.0); },
                o                  => { return o; },
            }
        }
    }
}


#[cfg_attr(feature = "trust_solver", trusted)]
#[ensures(match result {
    SatResult::Sat(assn) => { formula_sat_inner(@(^formula), @assn) && formula.equisat(^formula) },
    SatResult::Unsat     => { (^formula).not_satisfiable() && formula.equisat(^formula) },
    _                    => { true },
})]
pub fn solver(formula: &mut Formula) -> SatResult {
    match formula.check_formula_invariant() {
        SatResult::Unknown => {},
        o                  => { return o },
    }
    let mut trail = Trail::new(formula, Assignments::new(formula));
    let mut decisions = Decisions::new(formula);
    let mut watches = Watches::new(formula);
    watches.init_watches(formula);
    match trail.learn_units(formula, &mut decisions) {
        Some(cref) => {
            if derive_empty_formula(formula, &trail, cref) {
                return SatResult::Unsat;
            } else {
                // There is absolutely no way that this can happen, and it should pe provable
                return SatResult::Err;
            }
        }
        None => {}
    }
    let mut solver = Solver::new(formula); 
    solver.inner(formula, decisions, trail, watches)
}
