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

#[trusted] // TODO
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(trail.invariant(*f))]
#[requires((@trail.trail).len() > 0)]
#[requires(trail.trail_sem_invariant(*f, *a))]
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
    a.set_assignment(lit, f);
    trail.enq_assignment(lit, Reason::Unit, f, a);
}

#[trusted]

#[requires(trail.trail_sem_invariant(*f, *a))]
#[ensures((^trail).trail_sem_invariant(^f, ^a))]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(trail.invariant(*f))]
#[requires((@trail.trail).len() > 0)]
#[ensures((@(^trail).trail).len() === (@trail.trail).len())]
//#[ensures((@(^t).trail).len() >= (@t.trail).len())]
//#[ensures((^trail).invariant(*f))]
//#[ensures((^a).invariant(*f))]
#[ensures((*a).compatible(^a))]
#[ensures(f.eventually_sat_complete(*a) === (^f).eventually_sat_complete(^a))]
/*
#[ensures(match result { 
    ClauseState::Sat => f.sat(^self),
    ClauseState::Unsat => f.unsat(^self),
    ClauseState::Unknown => !(^self).complete(),
    ClauseState::Unit => !self.complete(),
    _ => true,
})^
*/
//#[ensures((a).complete() ==> *a === (^a) && ((result === ClauseState::Unsat) || f.sat(*self)))]
#[ensures(match result {
    Ok(()) => !(^f).unsat(^a),
    Err(n) => @n < (@f.clauses).len() && (^f).unsat(^a) && (@(^f).clauses)[@n].unsat(*a),
})]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures((^f).invariant())]
#[ensures(^f === *f)]
#[ensures(f.eventually_sat(*a) === (^f).eventually_sat(*a))]
#[ensures((^trail).invariant(^f))]
#[ensures((^a).invariant(^f))]
#[ensures(f.equisat_compatible(^f))]
fn unit_propagate(f: &mut Formula, a: &mut Assignments, trail: &mut Trail, watches: &mut Watches) -> Result<(), usize> {
    let mut i = 0;
    let d = trail.trail.len() - 1;
    while i < trail.trail[d].len() {
        let mut j = 0;
        let lit = trail.trail[d][i];
        let watchidx = lit.to_watchidx();
        'outer: while j < watches.watches[watchidx].len() {
            let cref = watches.watches[watchidx][j].cref;
            let first_lit = f.clauses[cref].rest[0];
            if first_lit.lit_sat(&a) {
                j += 1;
                continue;
            }
            let second_lit = f.clauses[cref].rest[1];
            if second_lit.lit_sat(&a) {
                // We swap to make it faster the next time
                f.clauses[cref].rest[0] = second_lit;
                f.clauses[cref].rest[1] = first_lit;
                j += 1;
                continue;
            }
            // At this point we know that none of the watched literals are sat
            let mut k = 2;
            let clause_len = f.clauses[cref].rest.len();
            while k < clause_len {
                let curr_lit = f.clauses[cref].rest[k];
                if a.0[curr_lit.idx] >= 2 || a.0[curr_lit.idx] == curr_lit.polarity as u8 { // Todo change
                    if first_lit.idx == lit.idx {
                        f.clauses[cref].rest[0] = curr_lit;
                        f.clauses[cref].rest[k] = first_lit;
                    } else {
                        f.clauses[cref].rest[0] = curr_lit;
                        f.clauses[cref].rest[k] = second_lit;
                        f.clauses[cref].rest[1] = first_lit;
                    }
                    // Update watch inlined
                    let end = watches.watches[watchidx].len() - 1;
                    watches.watches[watchidx].swap(j, end);
                    match watches.watches[watchidx].pop() {
                        Some(w) => {
                            watches.watches[curr_lit.to_neg_watchidx()].push(w);
                        },
                        None => {
                            unreachable!();
                        }
                    }
                    continue 'outer;
                }
                k += 1;
            }
            // If we have gotten here, the clause is either all false or unit
            if a.0[first_lit.idx] >= 2 {
                a.set_assignment(first_lit, f);
                trail.enq_assignment(first_lit, Reason::Long(cref), f, a);
            } else if a.0[second_lit.idx] >= 2 {
                f.clauses[cref].rest.swap(0,1);
                a.set_assignment(second_lit, f);
                trail.enq_assignment(second_lit, Reason::Long(cref), f, a);
            } else {
                return Err(cref);
            }
            j += 1;
        }
        i += 1;
    }
    Ok(())
}


//#[trusted] // OK(except for panic)
#[trusted] // tmp
#[ensures(match result {
    true  => { true },// !(^f).unsat(^a)}, // we dont know this
    false => { (^f).unsat(^a)},
})]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(t.invariant(*f))]
#[requires((@t.trail).len() > 0)]
#[requires(@cref < (@f.clauses).len())]
#[requires((@f.clauses)[@cref].unsat(*a))] // added
#[requires(t.trail_sem_invariant(*f, *a))] // added
#[ensures((^t).trail_sem_invariant(^f, ^a))] // added
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures((^f).invariant())]
//#[ensures(^f === *f)]
//#[ensures(f.eventually_sat(*a) === (^f).eventually_sat(*a))]
//#[ensures(f.eventually_sat_complete(*a) === (^f).eventually_sat_complete(*a))]
#[ensures((@(^t).trail).len() > 0)]
#[ensures((^t).invariant(^f))]
#[ensures((^a).invariant(^f))]
#[ensures(f.equisat_compatible(^f))]
fn handle_conflict(f: &mut Formula, a: &mut Assignments, t: &mut Trail, cref: usize, w: &mut Watches) -> bool {
    let res = analyze_conflict_new(f, a, t, cref);
    match res {
        Conflict::Ground => { 
            return false;
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
    _ => { return true;} // todo
    }
    true
}

#[trusted] // tmp
//#[trusted] // TMP, lacks trail
#[ensures(match result {
    Some(true)  => {!(^f).unsat(^a)}, // Prop went ok
    Some(false) => { (^f).unsat(^a)},
    None        => { true } // Continue
})]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(d.invariant(@f.num_vars))]
#[requires(t.invariant(*f))]
#[requires((@t.trail).len() > 0)]
#[requires(t.trail_sem_invariant(*f, *a))]
#[ensures((^t).trail_sem_invariant(^f, ^a))]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures((^f).invariant())]
//#[ensures(^f === *f)]
//#[ensures(f.eventually_sat(*a) === (^f).eventually_sat(*a))]
//#[ensures(f.eventually_sat_complete(*a) === (^f).eventually_sat_complete(*a))]
#[ensures((@(^t).trail).len() > 0)]
#[ensures((^t).invariant(^f))]
#[ensures((^a).invariant(^f))]
#[ensures(f.equisat_compatible(^f))]
fn unit_prop_step(f: &mut Formula, a: &mut Assignments, d: &Decisions, t: &mut Trail, w: &mut Watches) -> Option<bool> {
    match unit_propagate(f, a, t, w) {
    //match a.do_unit_propagation(f, t) {
        Ok(_) => {
            return Some(true);
        },
        Err(cref) => {
            if !handle_conflict(f, a, t, cref, w) {
                return Some(false);
            }
            None // Continue
        },
    }
}


//#[trusted] // OK (until trail)
#[ensures(!result ==> (^f).unsat(^a))]
#[ensures(result ==> !(^f).unsat(^a))]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(d.invariant(@f.num_vars))]
#[requires(t.invariant(*f))]
#[requires(t.trail_sem_invariant(*f, *a))]
#[ensures((^t).trail_sem_invariant(^f, ^a))]
#[requires((@t.trail).len() > 0)]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures((^f).invariant())]
//#[ensures(^f === *f)]
//#[ensures(f.eventually_sat(*a) === (^f).eventually_sat(*a))]
//#[ensures(f.eventually_sat_complete(*a) === (^f).eventually_sat_complete(*a))]
#[ensures((@(^t).trail).len() > 0)]
#[ensures((^t).invariant(^f))]
#[ensures((^a).invariant(^f))]
#[ensures(f.equisat_compatible(^f))]
fn unit_prop_loop(f: &mut Formula, a: &mut Assignments, d: &Decisions, t: &mut Trail, w: &mut Watches) -> bool {
    let old_f = Ghost::record(&f);
    let old_a = Ghost::record(&a);
    let old_t = Ghost::record(&t);
    //let old_w = Ghost::record(&w);
    //#[invariant(maintains_w, w.invariant(*f))]
    #[invariant(maintains_f, f.invariant())]
    #[invariant(maintains_a, a.invariant(*f))]
    #[invariant(maintains_t, t.invariant(*f))]
    #[invariant(maintains_t2, t.trail_sem_invariant(*f, *a))]
    #[invariant(vardata_unchanged, (@t.vardata).len() === (@(@old_t).vardata).len())]
    #[invariant(num_vars, @f.num_vars === @(@old_f).num_vars)]
    //#[invariant(clauses, (@f.clauses).len() > 0)]
    #[invariant(trail_len, (@t.trail).len() > 0)]
    #[invariant(propha, ^a === ^@old_a)]
    //#[invariant(prophw, ^w === ^@old_w)]
    #[invariant(prophf, ^f === ^@old_f)]
    #[invariant(propht, ^t === ^@old_t)]
    #[invariant(equi, (@old_f).equisat_compatible(*f))]
    loop {
        match unit_prop_step(f, a, d, t, w) {
            Some(true)  => { return true;  },
            Some(false) => { return false; },
            None        => {},
        }
    }
}


#[trusted] // OK
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(d.invariant(@f.num_vars))]
#[requires(t.invariant(*f))]
#[requires((@t.trail).len() > 0)]
#[requires(t.trail_sem_invariant(*f, *a))]
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
    Some(true)  => { (^f).sat(^a) && (^a).complete() },
    Some(false) => { (^f).unsat(^a)}, // ground conflict
    None        => {true}  // we know something
})]
#[ensures(f.equisat_compatible(^f))]
fn outer_loop(f: &mut Formula, a: &mut Assignments, d: &Decisions, t: &mut Trail, w: &mut Watches) -> Option<bool> {
    match unit_prop_loop(f, a, d, t, w) {
        false => return Some(false),
        _ => {}
    }
    //proof_assert!(!a.complete() || !f.unsat(*a)); // Need to get from unit_prop_loop
    match a.find_unassigned(d, f) {
        Some(next) => {
            let dlevel = t.trail.len();
            //t.trail.push(Vec::new());
            t.add_level(f);
            // TODO DO A PROOF HERE
            // Have to do a proof to an unassigned cannot affect any post_units
            // VC Checks out, but it is slow.
            a.0[next] = 1; 
            let lit = Lit{ idx: next, polarity: true };
            proof_assert!(t.trail_sem_invariant(*f, *a));
            t.enq_assignment(lit, Reason::Decision, f, a);
        },
        None => { 
            // This is gonna get broken if one changes the definition of unsat
            proof_assert!(a.complete());
            proof_assert!(!f.unsat(*a));
            proof_assert!(lemma_complete_and_not_unsat_implies_sat(*f, @a); true);
            return Some(true); 
        },
    }
    None
}

#[trusted] // OK
//#[trusted] // tmp (mostly ok)
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(d.invariant(@f.num_vars))]
#[requires(t.invariant(*f))]
#[requires((@t.trail).len() > 0)]
#[requires(t.trail_sem_invariant(*f, *a))]
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
    true => { (^f).sat(^a) && f.sat(^a) && f.eventually_sat_complete_no_ass()},
    false => { (^f).unsat(^a) }// && f.unsat(^a)}, // + add resolution from empty clause
})]
#[ensures(f.equisat_compatible(^f))]
fn inner(f: &mut Formula, a: &mut Assignments, d: &Decisions, t: &mut Trail, w: &mut Watches) -> bool {
    let old_f = Ghost::record(&f);
    let old_a = Ghost::record(&a);
    let old_t = Ghost::record(&t);
    //let old_w = Ghost::record(&w);
    //#[invariant(maintains_w, watches.invariant(*f))]
    //#[invariant(clauses, (@f.clauses).len() > 0)]
    //#[invariant(prophw, ^w === ^@old_w)]
    #[invariant(maintains_f, f.invariant())]
    #[invariant(maintains_a, a.invariant(*f))]
    #[invariant(maintains_t, t.invariant(*f))]
    #[invariant(maintains_t2, t.trail_sem_invariant(*f, *a))]
    #[invariant(vardata_unchanged, (@t.vardata).len() === (@(@old_t).vardata).len())]
    #[invariant(num_vars, @f.num_vars === @(@old_f).num_vars)]
    #[invariant(trail_len, (@t.trail).len() > 0)]
    #[invariant(propha, ^a === ^@old_a)]
    #[invariant(prophf, ^f === ^@old_f)]
    #[invariant(propht, ^t === ^@old_t)]
    #[invariant(equi, (@old_f).equisat_compatible(*f))]
    loop {
        let res = outer_loop(f, a, d, t, w);
        match res {
            Some(true)  => { return true;  },
            Some(false) => { return false; },
            None        => {},
        }
    }
}

#[trusted]
pub fn solver(f: &mut Formula, units: &std::vec::Vec<Lit>) -> bool {
    // should do pure literal and identifying unit clauses in preproc
    let mut i = 0;
    let mut assignments = Assignments::new(f);
    let mut trail = Trail::new(f, &assignments);
    if f.num_vars == 0 {
        return true;
    }
    let mut watches = Watches::new(f);
    watches.init_watches(f);
    let decisions = Decisions::new(f);
    while i < units.len() {
        trail.enq_assignment(units[i], Reason::Unit, f, &assignments);
        let lit = units[i];
        learn_unit(&mut assignments, &mut trail, lit, f);
        i += 1;
    }
    if units.len() > 0 {
        panic!();
    }
    inner(f, &mut assignments, &decisions, &mut trail, &mut watches)
}