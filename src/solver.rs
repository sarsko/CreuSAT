extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{
    lit::*,
    clause::*,
    assignments::*,
    formula::*,
    logic::*,
    decision::*,
    trail::*,
    watches::*,
    conflict_analysis::*,
    unit_prop::*,
};

// Tmp
#[cfg(contracts)]
use crate::logic::{
    logic::*,
    logic_formula::*,
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

// This is OK except that we don't have a notion for unsat
#[cfg_attr(all(any(trust_solver, trust_all), not(untrust_all)), trusted)]
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
        },
        Conflict::Unit(clause) => {
            // Have to do a proof that it isnt already unit?
            let cref = f.add_unit(clause, t);
            t.learn_unit(cref, f);
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
        Conflict::Panic => { return Some(true); }
    }
    None
}

// OK
#[cfg_attr(all(any(trust_solver, trust_all), not(untrust_all)), trusted)]
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
fn unit_prop_step(f: &mut Formula, d: &Decisions, t: &mut Trail, w: &mut Watches) -> ConflictResult {
    return match unit_propagate(f, t, w) {
    //match a.do_unit_propagation(f, t) {
        Ok(_) => ConflictResult::Ok,
        Err(cref) => {
            match handle_conflict(f, t, cref, w) {
                Some(false) => ConflictResult::Ground,
                Some(true)  => ConflictResult::Err,
                None        => ConflictResult::Continue,
            }
        },
    }
}

// OK
#[cfg_attr(all(any(trust_solver, trust_all), not(untrust_all)), trusted)]
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
            ConflictResult::Ok       => { return Some(true);  },
            ConflictResult::Ground   => { return Some(false); },
            ConflictResult::Err      => { return None; },
            ConflictResult::Continue => {},
        }
    }
}


// OK
#[cfg_attr(all(any(trust_solver, trust_all), not(untrust_all)), trusted)]
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
        None        => return SatResult::Err,
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
        },
        None => { 
            // This is gonna get broken if one changes the definition of unsat
            // Okay so this got broken from unit prop not returning full eval anymore.
            // Seems like we either have to become ternary and do a check(which cannot fail)
            // or do a rather long proof about the correctness of watched literals
            //proof_assert!(a.complete());
            //proof_assert!(!f.unsat(*a));
            //proof_assert!(lemma_complete_and_not_unsat_implies_sat(*f, @a); true);
            if f.is_sat(&trail.assignments) {
                return SatResult::Sat(Vec::new()); // TODO add sat assignment
            } else {
                return SatResult::Err; // This should never happen
            }
        },
    }
    SatResult::Unknown
}

// OK
#[cfg_attr(all(any(trust_solver, trust_all), not(untrust_all)), trusted)]
#[requires(@formula.num_vars < @usize::MAX/2)]
#[requires(formula.invariant())]
#[requires(decisions.invariant(@formula.num_vars))]
#[requires(trail.invariant(*formula))]
#[requires(watches.invariant(*formula))]
// No point in ensuring these for our uses, but they are strictly speaking ensured
//#[ensures(@f.num_vars === @(^f).num_vars)]
//#[ensures((^f).invariant())]
//#[ensures(^f === *f)]
//#[ensures(f.eventually_sat(*a) === (^f).eventually_sat(*a))]
//#[ensures(f.eventually_sat_complete(*a) === (^f).eventually_sat_complete(*a))]
//#[ensures((@(^t).trail).len() >= (@t.trail).len())]
//#[ensures((^t).invariant(^f))]
//#[ensures((^a).invariant(^f))]
//#[ensures((^d).invariant())]
//#[ensures(result === true ==> f.eventually_sat(*a))]
//#[ensures(result === false ==> !f.eventually_sat_complete(*a))]
#[ensures(match result {
    SatResult::Sat(_) => { (^formula).sat((^trail).assignments) && formula.equisat(^formula) && formula.eventually_sat_complete_no_ass()}, // TODO: + vec is assign
    SatResult::Unsat => { (^formula).not_satisfiable() && formula.equisat(^formula) }
    _ => true,
})]
#[ensures(formula.equisat(^formula))]
fn inner(formula: &mut Formula, decisions: &Decisions, trail: &mut Trail, watches: &mut Watches) -> SatResult {
    let old_f = Ghost::record(&formula);
    let old_t = Ghost::record(&trail);
    let old_w = Ghost::record(&watches);
    #[invariant(equi, (@old_f).equisat(*formula))]
    #[invariant(num_vars, @formula.num_vars === @(@old_f).num_vars)]
    #[invariant(maintains_f, formula.invariant())]
    #[invariant(maintains_t, trail.invariant(*formula))]
    #[invariant(maintains_w, watches.invariant(*formula))]
    #[invariant(prophf, ^formula === ^@old_f)]
    #[invariant(propht, ^trail === ^@old_t)]
    #[invariant(prophw, ^watches === ^@old_w)]
    loop {
        match outer_loop(formula, decisions, trail, watches) {
            SatResult::Unknown => {}, // continue
            o => return o,
        }
    }
}

// TODO on this. Look at it after figuring out UNSAT
// (does check out btw)
//#[cfg_attr(all(any(trust_solver, trust_all), not(untrust_all)), trusted)]
#[requires(formula.invariant())]
#[ensures(match result {
    SatResult::Sat(assn) => { formula_sat_inner(@(^formula), @assn) && formula.equisat(^formula) && formula.eventually_sat_complete_no_ass()}, // TODO: + vec is assign
    SatResult::Unsat => { (^formula).not_satisfiable() && formula.equisat(^formula) }
    _ => true,
})]
pub fn solver(formula: &mut Formula) -> SatResult {
    // Swapping to not needing binary clauses seem to have gone fine.
    // Should undo the split to units, then do an init function which
    // watches the at least binary clauses and adds the units as unit.
    // As for the learnt units, I think those should be added to the formula as well,
    // and then finally one does a resolution from the last conflict to the empty clause,
    // which combined with transitive equisat means that the formula is unsat.
    // Great success,
    let mut i = 0;
    let mut trail = Trail::new(formula, Assignments::new(formula));
    if formula.num_vars >= usize::MAX/2 {
        return SatResult::Err;
    }
    // Should ideally do a check for if num_vars is correct and everything here. Ah well, todo
    if formula.num_vars == 0 {
        return SatResult::Sat(Vec::new());
    }
    let decisions = Decisions::new(formula);
    let mut watches = Watches::new(formula);
    watches.init_watches(formula);
    match trail.learn_units(formula) {
        false => {
            return SatResult::Unsat; // TODO on proving this(should be simple, we have conflict between two units(make it a special enum?))
        }
        true => {},
    }
    inner(formula, &decisions, &mut trail, &mut watches)
}