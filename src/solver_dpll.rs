extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::lit::*;
use crate::clause::*;
use crate::assignments::*;
use crate::formula::*;
use crate::logic::*;
use crate::decision::*;

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
#[ensures((^a).invariant(*f))]
//#[ensures((^d).invariant())]
#[ensures(result === true ==> f.eventually_sat(*a))]
#[ensures(result === false ==> !f.eventually_sat_complete(*a))]
fn inner(f: &Formula, a: &mut Assignments, d: &Decisions) -> bool {
    a.do_unit_propagation(f);
    match f.eval(a) {
        SatState::Sat => return true,
        SatState::Unsat => return false,
        _ => {}
    };
    let mut a_cloned = a.clone();
    let next = a.find_unassigned(d, f);
    a.0[next] = 1;
    a_cloned.0[next] = 0;

    if inner(f, a, d) {
        return true;
    } else {
        return inner(f, &mut a_cloned, d);
    }
}

#[trusted]
pub fn solver(f: &Formula, units: &std::vec::Vec<Lit>) -> bool {
    // should do pure literal and identifying unit clauses in preproc
    if units.len() > 0 {
        panic!();
    }
    if f.num_vars == 0 {
        return true;
    }
    let mut assignments = Assignments::new(f);
    let decisions = Decisions::new(f);
    inner(f, &mut assignments, &decisions)
}