extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::lit::*;
use crate::clause::*;
use crate::assignments::*;
use crate::formula::*;
use crate::logic::*;
use crate::decision::*;
use crate::trail::*;
use crate::watches::*;
use crate::conflict_analysis::*;
use crate::unit_prop::*;

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

#[trusted] // OK
#[ensures(result === (@f.clauses)[@idx].sat(*a))]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(@idx < (@f.clauses).len())]
pub fn is_clause_sat(f: &Formula, idx: usize, a: &Assignments) -> bool {
    let clause = &f.clauses[idx];
    let mut i: usize = 0;
    #[invariant(previous, forall<j: Int> 0 <= j && j < @i ==> !(@clause)[j].sat(*a))]
    while i < clause.rest.len() {
        if clause.rest[i].lit_sat(a) {
            return true;
        }
        i += 1;
    }
    return false;
}

#[trusted] // OK
#[ensures(result === (@f.clauses)[@idx].unsat(*a))]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(@idx < (@f.clauses).len())]
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

#[trusted] // Small --TODO--
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(trail.invariant(*f))]
#[requires((@trail.trail).len() > 0)]
#[requires(trail.trail_sem_invariant(*f, *a))]
#[requires(0 <= @lit.idx && @lit.idx < (@a).len())] // added
#[ensures((^trail).trail_sem_invariant(*f, ^a))]
#[ensures((@(^trail).trail).len() === 1)]
//#[ensures(^f === *f)]
//#[ensures(f.eventually_sat(*a) === (^f).eventually_sat(*a))]
//#[ensures(f.eventually_sat_complete(*a) === (^f).eventually_sat_complete(*a))]
#[ensures((^trail).invariant(*f))]
#[ensures((^a).invariant(*f))]
pub fn learn_unit(a: &mut Assignments, trail: &mut Trail, lit: Lit, f: &Formula) {
    //a.cancel_until(trail, trail.trail.len(), 1, decisions);
    a.cancel_until(trail, 1, f);
    //a.cancel_long(trail);
    // TODO fix precond for lit unset
    a.set_assignment(lit, f, trail); 
    trail.enq_assignment(lit, Reason::Unit, f, a);
}

#[trusted] // OK(except for panic)
#[ensures(match result {
    Some(false) => { (^f).unsat(^a)},
    Some(true)  => { true },
    None        => { true }, // !(^f).unsat(^a)}, // we dont know this
})]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(t.invariant(*f))]
#[requires(w.invariant(*f))]
#[requires((@t.trail).len() > 0)]
#[requires(@cref < (@f.clauses).len())]
#[requires((@f.clauses)[@cref].unsat(*a))] // added
#[requires(t.trail_sem_invariant(*f, *a))] // added
#[ensures((^t).trail_sem_invariant(^f, ^a))] // added
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures((^f).invariant())]
#[ensures((^a).invariant(^f))]
#[ensures((^t).invariant(^f))]
#[ensures((^w).invariant(^f))] 
#[ensures((@(^t).trail).len() > 0)]
#[ensures(f.equisat_compatible(^f))]
fn handle_conflict(f: &mut Formula, a: &mut Assignments, t: &mut Trail, cref: usize, w: &mut Watches) -> Option<bool> {
    let res = analyze_conflict(f, a, t, cref);
    match res {
        Conflict::Ground => { 
            return Some(false);
        },
        Conflict::Unit(lit) => {
            learn_unit(a, t, lit, f);
        }
        Conflict::Learned(level, lit, clause) => {
            // Okay so doing a full search restart every time is a lot less slow than expected
            // and is very simple. If I make the proof of resolution from init to empty clause/
            // ground conflict work, then everything else can be treated as optimizations
            let cref = f.add_clause(clause, w, t);
            a.cancel_until(t, 1, f);
            //println!("Learned clause {:?}", clause);
            //decisions.increment_and_move(f, cref);
            //a.cancel_until(t, level, f);
            //t.add_level(f);
            //a.set_assignment(lit, f);
            //proof_assert!(@cref < (@f.clauses).len());
            //t.enq_assignment(lit, Reason::Long(cref), f);
        }
        Conflict::Panic => { return Some(true); }
    }
    None
}

#[trusted] // OK
#[requires(@f.num_vars < @usize::MAX/2)]
#[ensures(match result {
    ConflictResult::Ground => { (^f).unsat(^a)},
    _                      => { true }
})]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(d.invariant(@f.num_vars))]
#[requires(t.invariant(*f))]
#[requires((@t.trail).len() > 0)]
#[requires(t.trail_sem_invariant(*f, *a))]
#[requires(w.invariant(*f))]
#[ensures((^w).invariant(^f))]
#[ensures((^t).trail_sem_invariant(^f, ^a))]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures((^f).invariant())]
#[ensures((@(^t).trail).len() > 0)]
#[ensures((^t).invariant(^f))]
#[ensures((^a).invariant(^f))]
#[ensures(f.equisat(^f))]
fn unit_prop_step(f: &mut Formula, a: &mut Assignments, d: &Decisions, t: &mut Trail, w: &mut Watches) -> ConflictResult {
    match unit_propagate(f, a, t, w) {
    //match a.do_unit_propagation(f, t) {
        Ok(_) => {
            return ConflictResult::Ok;
        },
        Err(cref) => {
            return match handle_conflict(f, a, t, cref, w) {
                Some(false) => ConflictResult::Ground,
                Some(true)  => ConflictResult::Err,
                None        => ConflictResult::Continue,
            };
        },
    }
}


#[trusted] // OK
#[requires(@f.num_vars < @usize::MAX/2)]
//#[ensures(result ==> !(^f).unsat(^a))]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(d.invariant(@f.num_vars))]
#[requires(t.invariant(*f))]
#[requires(t.trail_sem_invariant(*f, *a))]
#[requires((@t.trail).len() > 0)]
#[requires(w.invariant(*f))]
#[ensures((^w).invariant(^f))]
#[ensures((^t).trail_sem_invariant(^f, ^a))]
#[ensures(match result {
    Some(false) => { (^f).unsat(^a)},
    Some(true)  => { true },
    None        => { true }, 
})]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures((^f).invariant())]
#[ensures((@(^t).trail).len() > 0)]
#[ensures((^t).invariant(^f))]
#[ensures((^a).invariant(^f))]
#[ensures(f.equisat(^f))]
fn unit_prop_loop(f: &mut Formula, a: &mut Assignments, d: &Decisions, t: &mut Trail, w: &mut Watches) -> Option<bool> {
    let old_f = Ghost::record(&f);
    let old_a = Ghost::record(&a);
    let old_t = Ghost::record(&t);
    let old_w = Ghost::record(&w);
    #[invariant(prophf, ^f === ^@old_f)]
    #[invariant(propha, ^a === ^@old_a)]
    #[invariant(propht, ^t === ^@old_t)]
    #[invariant(prophw, ^w === ^@old_w)]
    #[invariant(maintains_f, f.invariant())]
    #[invariant(maintains_a, a.invariant(*f))]
    #[invariant(maintains_t, t.invariant(*f))]
    #[invariant(maintains_w, w.invariant(*f))]
    #[invariant(maintains_t2, t.trail_sem_invariant(*f, *a))]
    #[invariant(equi, (@old_f).equisat(*f))]
    #[invariant(trail_len, (@t.trail).len() > 0)]
    #[invariant(num_vars, @f.num_vars === @(@old_f).num_vars)]
    #[invariant(vardata_unchanged, (@t.vardata).len() === (@(@old_t).vardata).len())]
    loop {
        match unit_prop_step(f, a, d, t, w) {
            ConflictResult::Ok       => { return Some(true);  },
            ConflictResult::Ground   => { return Some(false); },
            ConflictResult::Err      => { return None; },
            ConflictResult::Continue => {},
        }
    }
}


#[trusted] // --TODO--: Only thing missing is the assertion of sat
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(d.invariant(@f.num_vars))]
#[requires(t.invariant(*f))]
#[requires((@t.trail).len() > 0)]
#[requires(t.trail_sem_invariant(*f, *a))]
#[requires(w.invariant(*f))]
#[ensures((^w).invariant(^f))]
#[ensures((^t).trail_sem_invariant(^f, ^a))]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures((^f).invariant())]
//#[ensures(^f === *f)]
//#[ensures(f.eventually_sat(*a) === (^f).eventually_sat(*a))]
//#[ensures(f.eventually_sat_complete(*a) === (^f).eventually_sat_complete(*a))]
#[ensures((@(^t).trail).len() > 0)]
#[ensures((^t).invariant(^f))]
#[ensures((^a).invariant(^f))]
#[ensures(match result {
    SatResult::Sat(_)   => { (^f).sat(^a) && (^a).complete() }, // TODO: Vec is sat assign
    SatResult::Unsat    => { (^f).unsat(^a)}, // ground conflict
    SatResult::Unknown  => {true}
    SatResult::Err      => { true }
})]
#[ensures(f.equisat(^f))]
fn outer_loop(f: &mut Formula, a: &mut Assignments, d: &Decisions, t: &mut Trail, w: &mut Watches) -> SatResult {
    match unit_prop_loop(f, a, d, t, w) {
        Some(false) => return SatResult::Unsat,
        None        => return SatResult::Err,
        _ => {}
    }
    //proof_assert!(!a.complete() || !f.unsat(*a)); // Need to get from unit_prop_loop
    match a.find_unassigned(d, f) {
        Some(next) => {
            let dlevel = t.trail.len();
            //t.trail.push(Vec::new());
            t.add_level(f);
            // zzTODOzz DO A PROOF HERE
            // Have to do a proof to an unassigned cannot affect any post_units
            // VC Checks out, but it is slow.
            let lit = Lit{ idx: next, polarity: a.0[next] == 3 };
            a.0[next] -= 2;
            t.enq_assignment(lit, Reason::Decision, f, a);
            proof_assert!(t.trail_sem_invariant(*f, *a));
        },
        None => { 
            // This is gonna get broken if one changes the definition of unsat
            // Okay so this got broken from unit prop not returning full eval anymore.
            // Seems like we either have to become ternary and do a check(which cannot fail)
            // or do a rather long proof about the correctness of watched literals
            proof_assert!(a.complete());
            proof_assert!(!f.unsat(*a));
            proof_assert!(lemma_complete_and_not_unsat_implies_sat(*f, @a); true);
            return SatResult::Sat(Vec::new()); // TODO add sat assignment
        },
    }
    SatResult::Unknown
}

#[trusted] // OK
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(d.invariant(@f.num_vars))]
#[requires(t.invariant(*f))]
#[requires((@t.trail).len() > 0)]
#[requires(t.trail_sem_invariant(*f, *a))]
#[requires(w.invariant(*f))]
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
    SatResult::Sat(_) => { (^f).sat(^a) && f.equisat(^f) && f.eventually_sat_complete_no_ass()}, // TODO: + vec is assign
    SatResult::Unsat => { (^f).unsat(^a) }// && f.unsat(^a)}, // + add resolution from empty clause
    _ => true,
})]
#[ensures(f.equisat(^f))]
fn inner(f: &mut Formula, a: &mut Assignments, d: &Decisions, t: &mut Trail, w: &mut Watches) -> SatResult {
    let old_f = Ghost::record(&f);
    let old_a = Ghost::record(&a);
    let old_t = Ghost::record(&t);
    let old_w = Ghost::record(&w);
    #[invariant(prophf, ^f === ^@old_f)]
    #[invariant(propha, ^a === ^@old_a)]
    #[invariant(propht, ^t === ^@old_t)]
    #[invariant(prophw, ^w === ^@old_w)]
    #[invariant(maintains_f, f.invariant())]
    #[invariant(maintains_a, a.invariant(*f))]
    #[invariant(maintains_t, t.invariant(*f))]
    #[invariant(maintains_w, w.invariant(*f))]
    #[invariant(maintains_t2, t.trail_sem_invariant(*f, *a))]
    #[invariant(equi, (@old_f).equisat(*f))]
    #[invariant(trail_len, (@t.trail).len() > 0)]
    #[invariant(num_vars, @f.num_vars === @(@old_f).num_vars)]
    #[invariant(vardata_unchanged, (@t.vardata).len() === (@(@old_t).vardata).len())]
    loop {
        match outer_loop(f, a, d, t, w) {
            SatResult::Unknown => {}, // continue
            o => return o,
        }
    }
}

//#[trusted] // xxTODOxx
#[requires(forall<i: Int> 0 <= i && i < (@units).len() ==>
    @(@units)[i].idx < @f.num_vars
)]
#[requires(f.invariant())] // Not fully correct, need a smaller invariant
pub fn solver(f: &mut Formula, units: &std::vec::Vec<Lit>) -> SatResult {
    // should do pure literal and identifying unit clauses in preproc
    let mut i = 0;
    let mut assignments = Assignments::new(f);
    let mut trail = Trail::new(f, &assignments);
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
    #[invariant(trail_inv, trail.invariant(*f))]
    #[invariant(trail_sem, trail.trail_sem_invariant(*f, assignments))]
    #[invariant(ass_inv, assignments.invariant(*f))]
    #[invariant(trail_len, (@trail.trail).len() === 1)]
    while i < units.len() {
        trail.enq_assignment(units[i], Reason::Unit, f, &assignments);
        let lit = units[i];
        learn_unit(&mut assignments, &mut trail, lit, f);
        i += 1;
    }
    /*
    if units.len() > 0 {
        panic!();
    }
    */
    inner(f, &mut assignments, &decisions, &mut trail, &mut watches)
}