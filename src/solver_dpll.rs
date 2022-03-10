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
pub fn learn_unit(a: &mut Assignments, trail: &mut Trail, lit: Lit, f: &Formula) {
    //a.cancel_until(trail, trail.trail.len(), 1, decisions);
    a.cancel_until(trail, 1, f);
    //a.cancel_long(trail);
    a.set_assignment(lit, f);
    trail.enq_assignment(lit, Reason::Unit, f);
}
#[trusted]

#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(trail.invariant(*f))]
#[requires((@trail.trail).len() > 0)]
#[ensures((@(^trail).trail).len() === (@trail.trail).len())]
#[ensures((^trail).invariant(*f))]
#[ensures((^a).invariant(*f))]
#[ensures(f.eventually_sat_complete(^a) === f.eventually_sat_complete(*a))]
#[ensures((*a).compatible(^a))]
/*
#[ensures(match result { 
    ClauseState::Sat => f.sat(^self),
    ClauseState::Unsat => f.unsat(^self),
    ClauseState::Unknown => !(^self).complete(),
    ClauseState::Unit => !self.complete(),
    _ => true,
})]
*/
//#[ensures((a).complete() ==> *a === (^a) && ((result === ClauseState::Unsat) || f.sat(*self)))]
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
                trail.enq_assignment(first_lit, Reason::Long(cref), f);
            } else if a.0[second_lit.idx] >= 2 {
                f.clauses[cref].rest.swap(0,1);
                a.set_assignment(second_lit, f);
                trail.enq_assignment(second_lit, Reason::Long(cref), f);
            } else {
                return Err(cref);
            }
            j += 1;
        }
        i += 1;
    }
    Ok(())
}

fn unit_prop_step(f: &mut Formula, a: &mut Assignments, d: &Decisions, t: &mut Trail, w: &mut Watches) -> Option<bool> {
    match unit_propagate(f, a, t, w) {
    //match a.do_unit_propagation(f, t) {
        Ok(_) => {
            return Some(true);
        },
        Err(cref) => {
            // Abstract this away further
            match analyze_conflict(f, a, t, cref) {
                Conflict::Ground => { 
                    return Some(false);
                },
                    Conflict::Unit(lit) => {
                        learn_unit(a, t, lit, f);
                    }
                    Conflict::Learned(level, lit, clause) => {
                        let cref = f.add_clause(&clause, w);
                        //decisions.increment_and_move(f, cref);
                        //a.cancel_until(trail, trail.trail.len(), level, decisions);
                        a.cancel_until(t, level, f);
                        t.trail.push(Vec::new());
                        a.set_assignment(lit, f);
                        t.enq_assignment(lit, Reason::Long(cref), f);
                    }
                    _ => panic!()
            }
        },
    }
    None
}

fn unit_prop_loop(f: &mut Formula, a: &mut Assignments, d: &Decisions, t: &mut Trail, w: &mut Watches) -> bool {
    loop {
        match unit_prop_step(f, a, d, t, w) {
            Some(true) => {
                return true;
            },
            Some(false) => {
                return false;
            },
            None => {}
        }
    }
}

fn outer_loop(f: &mut Formula, a: &mut Assignments, d: &Decisions, t: &mut Trail, w: &mut Watches) -> Option<bool> {
    match unit_prop_loop(f, a, d, t, w) {
        false => return Some(false),
        _ => {}
    }
    proof_assert!(!a.complete() || !f.unsat(*a));
    match a.find_unassigned(d, f) {
        Some(next) => {
            let dlevel = t.trail.len();
            t.trail.push(Vec::new());
            a.0[next] = 1; 
            let lit = Lit{ idx: next, polarity: true };
            t.enq_assignment(lit, Reason::Decision, f);
            //let old_a = Ghost::record(&a);
            //let mut a_cloned = a.clone();
            //proof_assert!(@a_cloned === @@old_a);
            //t.add_level(f);
            //let old_a1 = a.1;
            /*
            return inner(f, a, d, t, w);
            if inner(f, a, d, t, w) {
                return true;
            }
            */
            /*
            a.cancel_until(t, dlevel, f);
            //proof_assert!(@a === @@old_a); // Todo on post for cancel_until
            t.add_level(f);
            a.0[next] = 0;
            //a_cloned.0[next] = 0;
            a.1 = old_a1;
            //a_cloned.1 = old_a1;
            let lit = Lit{ idx: next, polarity: false };
            t.enq_assignment(lit, Reason::Decision, f);
            //return inner(f, a, d, t, w);
            //return inner(f, &mut a_cloned, d, t, w);
            return inner(f, a, d, t, w);
            */
        },
        None => { 
            proof_assert!(a.complete());
            proof_assert!(!f.unsat(*a));
            proof_assert!(lemma_complete_and_not_unsat_implies_sat(*f, @a); true);
            return Some(true); 
        },
    }
    None
}

#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(d.invariant(@f.num_vars))]
#[requires(t.invariant(*f))]
#[requires((@t.trail).len() > 0)]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures((^f).invariant())]
#[ensures(^f === *f)]
#[ensures(f.eventually_sat(*a) === (^f).eventually_sat(*a))]
#[ensures(f.eventually_sat_complete(*a) === (^f).eventually_sat_complete(*a))]
#[ensures((@(^t).trail).len() >= (@t.trail).len())]
#[ensures((^t).invariant(^f))]
#[ensures((^a).invariant(^f))]
//#[ensures((^d).invariant())]
//#[ensures(result === true ==> f.eventually_sat(*a))]
//#[ensures(result === false ==> !f.eventually_sat_complete(*a))]
fn inner(f: &mut Formula, a: &mut Assignments, d: &Decisions, t: &mut Trail, w: &mut Watches) -> bool {
    let old_f = Ghost::record(&f);
    let old_a = Ghost::record(&a);
    let old_w = Ghost::record(&w);
    let old_t = Ghost::record(&t);
    #[invariant(maintains_f, f.invariant())]
    #[invariant(maintains_a, a.invariant(@f.num_vars))]
    #[invariant(maintains_t, trail.invariant(*f))]
    #[invariant(maintains_w, watches.invariant(*f))]
    #[invariant(vardata_unchanged, (@trail.vardata).len() === (@(@old_t).vardata).len())]
    #[invariant(num_vars, @f.num_vars === @(@old_f).num_vars)]
    #[invariant(clauses, (@f.clauses).len() > 0)]
    #[invariant(trail_len, (@trail.trail).len() > 0)]
    #[invariant(propha, ^a === ^@old_a)]
    #[invariant(prophw, ^watches === ^@old_w)]
    #[invariant(prophf, ^f === ^@old_f)]
    #[invariant(propht, ^trail === ^@old_t)]
    loop {
        let res = outer_loop(f, a, d, t, w);
        match res {
            Some(true) => {
                return true;
            },
            Some(false) => {
                return false;
            },
            None => {},
        }
    }
}

#[trusted]
pub fn solver(f: &mut Formula, units: &std::vec::Vec<Lit>) -> bool {
    // should do pure literal and identifying unit clauses in preproc
    let mut i = 0;
    let mut assignments = Assignments::new(f);
    let mut trail = Trail::new(f);
    if f.num_vars == 0 {
        return true;
    }
    let mut watches = Watches::new(f);
    watches.init_watches(f);
    let decisions = Decisions::new(f);
    while i < units.len() {
        trail.enq_assignment(units[i], Reason::Unit, f);
        let lit = units[i];
        learn_unit(&mut assignments, &mut trail, lit, f);
        i += 1;
    }
    if units.len() > 0 {
        panic!();
    }
    inner(f, &mut assignments, &decisions, &mut trail, &mut watches)
}