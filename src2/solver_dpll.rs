#![feature(type_ascription)]

extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;
use crate::lit::*;
use crate::clause::*;
use crate::assignments::*;
use crate::formula::*;
use crate::logic::*;

#[inline]
#[ensures(b ==> @result === 1)]
#[ensures(!b ==> @result === 0)]
pub fn bool_to_u8(b: bool) -> u8 {
    if b {
        1
    } else {
        0
    }
}

// OK
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(@idx < (@f.clauses).len())]
#[ensures(result === (@f.clauses)[@idx].sat(*a))]
pub fn is_clause_sat(f: &Formula, idx: usize, a: &Assignments) -> bool {
    let clause = &f.clauses[idx];
    if clause.first.lit_sat(a) || clause.second.lit_sat(a) {
        return true;
    }
    let mut i: usize = 0;
    #[invariant(previous, forall<j: Int> 0 <= j && j < @i ==>
        !(@clause.rest)[j].sat(*a)
    )]
    while i < clause.rest.len() {
        let lit = clause.rest[i];
        if lit.lit_sat(a) {
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
    if clause.first.lit_sat(a) || clause.second.lit_sat(a) {
        return false;
    }
    if a.0[clause.first.idx] >= 2 || a.0[clause.second.idx] >= 2 {
        return false;
    }
    let mut i: usize = 0;
    #[invariant(previous, forall<j: Int> 0 <= j && j < @i ==>
        (@clause.rest)[j].unsat(*a)
    )]
    while i < clause.rest.len() {
        let lit = clause.rest[i];
        if !lit.lit_unsat(a){
            return false;
        }
        i += 1;
    }
    return true;
}

#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[ensures((^a).invariant(*f))]
#[ensures(result ==> f.eventually_sat(*a))]
#[ensures(!result ==> !f.eventually_sat_complete(*a))]
fn inner(f: &Formula, a: &mut Assignments) -> bool {
    a.do_unit_propagation(f);
    match f.eval(a) {
        SatState::Sat => return true,
        SatState::Unsat => return false,
        _ => {}
    };
    let mut a_cloned = a.clone();
    let next = a.find_unassigned();
    a.0[next] = 1;
    a_cloned.0[next] = 0;

    if inner(f, a) {
        return true;
    } else {
        return inner(f, &mut a_cloned);
    }
}
