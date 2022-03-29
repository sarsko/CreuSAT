extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::lit::*;
use crate::clause::*;
use crate::assignments::*;
use crate::formula::*;
use crate::trail::*;
use crate::watches::*;

fn unit_prop_do_outer(f: &mut Formula, a: &mut Assignments, trail: &mut Trail, watches: &mut Watches, j: usize, watchidx: usize, lit: Lit) -> Result<bool, usize> {
    let cref = watches.watches[watchidx][j].cref;
    let first_lit = f.clauses[cref].rest[0];
    if first_lit.lit_sat(&a) {
        return Ok(true);
    }
    let second_lit = f.clauses[cref].rest[1];
    if second_lit.lit_sat(&a) {
        // We swap to make it faster the next time
        f.clauses[cref].rest[0] = second_lit;
        f.clauses[cref].rest[1] = first_lit;
        return Ok(true);
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
            return Ok(false) // dont increase j
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
    return Ok(true);
}

fn unit_prop_current_level(f: &mut Formula, a: &mut Assignments, trail: &mut Trail, watches: &mut Watches, i: usize, d: usize) -> Result<(), usize> {
    let mut j = 0;
    let lit = trail.trail[d][i];
    let watchidx = lit.to_watchidx();
    while j < watches.watches[watchidx].len() {
        if unit_prop_do_outer(f, a, trail, watches, j, watchidx, lit)? {
            j += 1;
        }
    }
    Ok(())
}

#[trusted] // WIP

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
pub fn unit_propagate_WIP(f: &mut Formula, a: &mut Assignments, trail: &mut Trail, watches: &mut Watches) -> Result<(), usize> {
    let mut i = 0;
    let d = trail.trail.len() - 1;
    while i < trail.trail[d].len() {
        unit_prop_current_level(f, a, trail, watches, i, d)?;
        i += 1;
    }
    Ok(())
}