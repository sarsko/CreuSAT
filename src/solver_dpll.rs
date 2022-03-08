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
#[ensures(result === true ==> f.eventually_sat(*a))]
#[ensures(result === false ==> !f.eventually_sat_complete(*a))]
fn inner(f: &mut Formula, a: &mut Assignments, d: &Decisions, t: &mut Trail, w: &mut Watches) -> bool {
    match a.do_unit_propagation(f, t) {
        Some(n) => { return n; },
        _ => {},
    }
    match a.find_unassigned(d, f) {
        Some(next) => {
            let dlevel = t.trail.len();
            let old_a = Ghost::record(&a);
            let mut a_cloned = a.clone();
            proof_assert!(@a_cloned === @@old_a);
            t.add_level(f);
            a.0[next] = 1;
            let lit = Lit{ idx: next, polarity: true };
            t.enq_assignment(lit, Reason::Decision, f);
            let old_a1 = a.1;
            if inner(f, a, d, t, w) {
                return true;
            }
            //a.cancel_until(t, dlevel, f);
            //proof_assert!(@a === @@old_a); // Todo on post for cancel_until
            t.add_level(f);
            //a.0[next] = 0;
            a_cloned.0[next] = 0;
            //a.1 = old_a1;
            a_cloned.1 = old_a1;
            let lit = Lit{ idx: next, polarity: false };
            t.enq_assignment(lit, Reason::Decision, f);
            //return inner(f, a, d, t, w);
            return inner(f, &mut a_cloned, d, t, w);
        },
        None => { return true; },
    }
}

#[trusted]
pub fn solver(f: &mut Formula, units: &std::vec::Vec<Lit>) -> bool {
    // should do pure literal and identifying unit clauses in preproc
    let mut i = 0;
    let mut assignments = Assignments::new(f);
    let mut trail = Trail::new(f);
    while i < units.len() {
        trail.enq_assignment(units[i], Reason::Unit, f);
        let lit = units[i];
        if lit.polarity {
            assignments.0[lit.idx] = 1;
        } else {
            assignments.0[lit.idx] = 0;
        }
    }
    /*
    if units.len() > 0 {
        panic!();
    }
    */
    if f.num_vars == 0 {
        return true;
    }
    let mut watches = Watches::new(f);
    let decisions = Decisions::new(f);
    inner(f, &mut assignments, &decisions, &mut trail, &mut watches)
}