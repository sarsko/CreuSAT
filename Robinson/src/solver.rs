extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::assignments::*;
use crate::clause::*;
use crate::decision::*;
use crate::formula::*;
use crate::lit::*;
use crate::logic::*;

#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(@idx < (@f.clauses).len())]
#[ensures(result === (@f.clauses)[@idx].sat(*a))]
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

#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(d.invariant(@f.num_vars))]
#[ensures(result === true ==> f.eventually_sat(a))]
#[ensures(result === false ==> !f.eventually_sat_complete(a))]
fn inner(f: &Formula, mut a: Assignments, d: &Decisions) -> bool {
    match a.do_unit_propagation(f) {
        Some(n) => {
            return n;
        }
        _ => {}
    }
    let next = a.find_unassigned(d, f);
    let old_a = Ghost::record(&a);
    let mut a_cloned = a.clone();
    //proof_assert!(@a_cloned === @@old_a);
    a.0[next] = 1;
    let lit = Lit {
        idx: next,
        polarity: true,
    };
    let old_a1 = a.1;
    if inner(f, a, d) {
        return true;
    }
    a_cloned.0[next] = 0;
    a_cloned.1 = old_a1;
    let lit = Lit {
        idx: next,
        polarity: false,
    };
    return inner(f, a_cloned, d);
}

#[trusted]
pub fn solver(f: &mut Formula, units: &Vec<Lit>) -> bool {
    // should do pure literal and identifying unit clauses in preproc
    let mut i = 0;
    let mut assignments = Assignments::new(f);
    while i < units.len() {
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
    let decisions = Decisions::new(f);
    inner(f, assignments, &decisions)
}
