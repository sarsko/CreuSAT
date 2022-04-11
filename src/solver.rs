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
};

pub enum SatResult {
    Sat(Vec<Lit>),
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

#[cfg_attr(all(any(trust_solver, trust_all), not(untrust_all)), trusted)]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(@idx < (@f.clauses).len())]
#[ensures(result === (@f.clauses)[@idx].unsat(*a))]
pub fn is_clause_unsat(f: &Formula, idx: usize, a: &Assignments) -> bool {
    let clause = &f.clauses[idx];
    let mut i: usize = 0;
    #[invariant(previous, forall<j: Int> 0 <= j && j < @i ==> (@clause)[j].unsat(*a))]
    while i < clause.rest.len() {
        if !clause.rest[i].lit_unsat(a) {
            return false;
        }
        i += 1;
    }
    return true;
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
    Some(false) => { false }, // Something has to be gotten from analyze conflict // This is wrong: (^f).unsat((^t).assignments)},
    Some(true)  => { true },
    None        => { true }, // !(^f).unsat(^a)}, // we dont know this
})]
fn handle_conflict(f: &mut Formula, t: &mut Trail, cref: usize, w: &mut Watches) -> Option<bool> {
    let res = analyze_conflict(f, t, cref);
    match res {
        Conflict::Ground => { 
            return Some(false);
        },
        Conflict::Unit(lit) => {
            // Have to do a proof that it isnt already unit?
            t.learn_unit(lit, f);
        }
        Conflict::Learned(level, lit, clause) => {
            // Okay so doing a full search restart every time is a lot less slow than expected
            // and is very simple. If I make the proof of resolution from init to empty clause/
            // ground conflict work, then everything else can be treated as optimizations

            // TODO
            let cref = f.add_clause(clause, w, t);
            //a.cancel_until(t, 1, f);

            // TODO: Has to be gotten from post of analyze
            //proof_assert!((@t.decisions).len() > @level);
            proof_assert!((@t.decisions).len() > 0);
            t.backtrack_to(0, f);
            //t.backtrack_to(1, f);
            /*
            t.backtrack_to(level, f);
            let step = Step{
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

// OK - Todo on unsat
#[cfg_attr(all(any(trust_solver, trust_all), not(untrust_all)), trusted)]
#[maintains((mut f).invariant())]
#[maintains((mut w).invariant(mut f))]
#[maintains((mut t).invariant(mut f))]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(d.invariant(@f.num_vars))] // d is here because it will later become mutable and updated in handle_conflict
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures(f.equisat(^f))]
#[ensures(match result {
    ConflictResult::Ground => { false }, // TODO on the unsat condition
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

// OK - TODO on the unsat condition
#[cfg_attr(all(any(trust_solver, trust_all), not(untrust_all)), trusted)]
#[maintains((mut f).invariant())]
#[maintains((mut t).invariant(mut f))]
#[maintains((mut w).invariant(mut f))]
#[requires(d.invariant(@f.num_vars))]
#[requires(@f.num_vars < @usize::MAX/2)]
#[ensures(match result {
    Some(false) => { false }, // TODO
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


// Ok. Again todo on post unsat
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
    SatResult::Unsat    => { false }, // TODO
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

// OK (again TODO on unsat)
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
    SatResult::Unsat => { false }// && f.unsat(^a)}, // + add resolution from empty clause
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
#[cfg_attr(all(any(trust_solver, trust_all), not(untrust_all)), trusted)]
#[requires(forall<i: Int> 0 <= i && i < (@units).len() ==>
    @(@units)[i].idx < @f.num_vars
)]
#[requires(f.invariant())] // Not fully correct, need a smaller invariant
pub fn solver(f: &mut Formula, units: &std::vec::Vec<Lit>) -> SatResult {
    // should do pure literal and identifying unit clauses in preproc
    let mut i = 0;
    let assignments = Assignments::new(f);
    let mut trail = Trail::new(f, assignments);
    if f.num_vars >= usize::MAX/2 {
        return SatResult::Err;
    }
    if f.num_vars == 0 {
        return SatResult::Sat(Vec::new());
    }
    let mut watches = Watches::new(f);
    watches.init_watches(f);
    let decisions = Decisions::new(f);
    // Todo on this
    // Okay so actually this is fine for semantics, we just have to include
    // it in the final check for sat and then return an error if they don't
    // match. For the unsat case, not including a clause can't make a sat formula
    // unsat
    //learn_unit(&mut assignments, &mut trail, lit, f);
    #[invariant(trail_inv, trail.invariant(*f))]
    while i < units.len() {
        let lit = units[i];
        trail.learn_unit(lit, f);
        i += 1;
    }
    /*
    if units.len() > 0 {
        panic!();
    }
    */
    inner(f, &decisions, &mut trail, &mut watches)
}