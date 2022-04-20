extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{
    assignments::*, clause::*, conflict_analysis::*, decision::*, formula::*, lit::*, logic::*,
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

// This is OK except that we don't have a notion for unsat
#[cfg_attr(feature = "trust_solver", trusted)]
#[maintains((mut f).invariant())]
#[maintains((mut t).invariant(mut f))]
#[maintains((mut w).invariant(mut f))]
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
fn handle_conflict(f: &mut Formula, t: &mut Trail, cref: usize, w: &mut Watches) -> Option<bool> {
    let res = analyze_conflict(f, t, cref);
    match res {
        Conflict::Ground => {
            return Some(false);
        }
        Conflict::Unit(clause) => {
            // Have to do a proof that it isnt already unit?
            let cref = f.add_unit(clause, t);
            match t.learn_unit(cref, f) {
                Err(_) => return Some(true),
                Ok(_) => {}
            }
        }
        Conflict::Learned(level, clause) => {
            // Okay so doing a full search restart every time is a lot less slow than expected
            // and is very simple. If I make the proof of resolution from init to empty clause/
            // ground conflict work, then everything else can be treated as optimizations

            let cref = f.add_clause(clause, w, t);

            t.backtrack_to(level, f);
            /*
            let step = Step {
                lit: lit,
                decision_level: level,
                reason: Reason::Long(cref),
            };
            t.enq_assignment(step, f);
            */

            //decisions.increment_and_move(f, cref);
            //a.cancel_until(t, level, f);
            //t.add_level(f);
            //a.set_assignment(lit, f);
            //proof_assert!(@cref < (@f.clauses).len());
            //t.enq_assignment(lit, reason::long(cref), f);
        }
        Conflict::Panic => {
            return Some(true);
        }
    }
    None
}

// OK
#[cfg_attr(feature = "trust_solver", trusted)]
#[maintains((mut f).invariant())]
#[maintains((mut w).invariant(mut f))]
#[maintains((mut t).invariant(mut f))]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(d.invariant(@f.num_vars))] // d is here because it will later become mutable and updated in handle_conflict
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures(f.equisat(^f))]
#[ensures(match result {
    ConflictResult::Ground => { (^f).not_satisfiable() },
    _                      => { true }
})]
fn unit_prop_step(
    f: &mut Formula,
    d: &Decisions,
    t: &mut Trail,
    w: &mut Watches,
) -> ConflictResult {
    return match unit_propagate(f, t, w) {
        //match a.do_unit_propagation(f, t) {
        Ok(_) => ConflictResult::Ok,
        Err(cref) => match handle_conflict(f, t, cref, w) {
            Some(false) => ConflictResult::Ground,
            Some(true) => ConflictResult::Err,
            None => ConflictResult::Continue,
        },
    };
}

// OK
#[cfg_attr(feature = "trust_solver", trusted)]
#[maintains((mut f).invariant())]
#[maintains((mut t).invariant(mut f))]
#[maintains((mut w).invariant(mut f))]
#[requires(d.invariant(@f.num_vars))]
#[requires(@f.num_vars < @usize::MAX/2)]
#[ensures(match result {
    Some(false) => { (^f).not_satisfiable() },
    Some(true)  => { true },
    None        => { true },
})]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures(f.equisat(^f))]
fn unit_prop_loop(f: &mut Formula, d: &Decisions, t: &mut Trail, w: &mut Watches) -> Option<bool> {
    let old_f = Ghost::record(&f);
    let old_t = Ghost::record(&t);
    let old_w = Ghost::record(&w);
    #[invariant(maintains_f, f.invariant())]
    #[invariant(maintains_t, t.invariant(*f))]
    #[invariant(maintains_w, w.invariant(*f))]
    #[invariant(equi, (@old_f).equisat(*f))]
    #[invariant(num_vars, @f.num_vars === @(@old_f).num_vars)]
    #[invariant(prophf, ^f === ^@old_f)]
    #[invariant(propht, ^t === ^@old_t)]
    #[invariant(prophw, ^w === ^@old_w)]
    loop {
        match unit_prop_step(f, d, t, w) {
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

// OK
#[cfg_attr(feature = "trust_solver", trusted)]
#[maintains((mut f).invariant())]
#[maintains((mut trail).invariant(mut f))]
#[maintains((mut w).invariant(mut f))]
#[requires(d.invariant(@f.num_vars))]
#[requires(@f.num_vars < @usize::MAX/2)]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures(f.equisat(^f))]
#[ensures(match result {
    SatResult::Sat(_)   => { (^f).sat((^trail).assignments)
        && ((^trail).assignments).complete() // Do I really need this for anything?
    }, // TODO: Vec is sat assign
    SatResult::Unsat    => { (^f).not_satisfiable() },
    SatResult::Unknown  => { true }
    SatResult::Err      => { true }
})]
fn outer_loop(f: &mut Formula, d: &Decisions, trail: &mut Trail, w: &mut Watches) -> SatResult {
    match unit_prop_loop(f, d, trail, w) {
        Some(false) => return SatResult::Unsat,
        None => return SatResult::Err,
        _ => {}
    }
    //proof_assert!(!a.complete() || !f.unsat(*a)); // Need to get from unit_prop_loop
    match trail.assignments.find_unassigned(d, f) {
        Some(next) => {
            //let dlevel = t.trail.len();
            //t.trail.push(Vec::new());
            //t.add_level(f);
            // zzTODOzz DO A PROOF HERE
            // Have to do a proof to an unassigned cannot affect any post_units
            // VC Checks out, but it is slow.
            // CHANGED
            //let lit = Lit{ idx: next, polarity: if trail.assignments.0[next] == 2 {false} else {true} }; // TODO encapsulate
            //trail.enq_decision(lit, f);
            trail.enq_decision(next, f);
            //t.assignments.0[next] -= 2;
            //t.enq_assignment(lit, Reason::Decision, f, a);
            //proof_assert!(t.trail_sem_invariant(*f, *a));
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
#[ensures(match result {
    SatResult::Sat(v) => { (^formula).sat_inner(@v) && formula.equisat(^formula) && formula.eventually_sat_complete_no_ass()},
    SatResult::Unsat => { (^formula).not_satisfiable() && formula.equisat(^formula) }
    _ => true,
})]
#[ensures(formula.equisat(^formula))]
fn inner(
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
    #[invariant(prophf, ^formula === ^@old_f)]
    loop {
        match outer_loop(formula, &decisions, &mut trail, &mut watches) {
            SatResult::Unknown => {} // continue
            SatResult::Sat(_) => {
                return SatResult::Sat(trail.assignments.0);
            }
            o => return o,
        }
    }
}

#[cfg_attr(feature = "trust_solved", trusted)]
#[requires(formula.invariant())]
#[ensures(match result {
    SatResult::Sat(assn) => { formula_sat_inner(@(^formula), @assn) && formula.equisat(^formula) },
    SatResult::Unsat => { (^formula).not_satisfiable() && formula.equisat(^formula) }
    _ => true,
})]
pub fn solver(formula: &mut Formula) -> SatResult {
    let mut trail = Trail::new(formula, Assignments::new(formula));
    if formula.num_vars >= usize::MAX / 2 {
        return SatResult::Err;
    }
    // Should do a check for if num_vars is correct and everything here. Ah well, todo
    if formula.clauses.len() == 0 {
        let a: Vec<AssignedState> = Vec::new();
        return SatResult::Sat(a);
    }
    let decisions = Decisions::new(formula);
    let mut watches = Watches::new(formula);
    watches.init_watches(formula);
    match trail.learn_units(formula) {
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
    inner(formula, decisions, trail, watches)
}
