extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::lit::*;
use crate::clause::*;
use crate::assignments::*;
use crate::formula::*;
use crate::logic::*;

#[ensures(result === (@f.clauses)[@idx].sat(*a))]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(@idx < (@f.clauses).len())]
pub fn is_clause_sat(f: &Formula, idx: usize, a: &Assignments) -> bool {
    /*
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
    */
    let clause = &f.clauses[idx];
    proof_assert!(lemma_alt_equi(*clause, *a);true);
    proof_assert!(lemma_alt_sat_equi(*clause, *a);true);
    proof_assert!(lemma_alt_sat_equi_opp(*clause, *a);true);
    if clause.first.lit_sat(a) || clause.second.lit_sat(a) {
        proof_assert!(clause.sat(*a));
        return true;
    }
    let mut i: usize = 0;
    #[invariant(previous, forall<j: Int> 0 <= j && j < @i ==>
        !(@clause.rest)[j].sat(*a)
    )]
    while i < clause.rest.len() {
        let lit = clause.rest[i];
        if lit.lit_sat(a) {
            proof_assert!(clause.sat(*a));
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
    /*
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
    */
    let clause = &f.clauses[idx];
    proof_assert!(lemma_alt_equi(*clause, *a);true);
    proof_assert!(lemma_alt_unsat_equi(*clause, *a);true);
    proof_assert!(lemma_alt_unsat_equi_opp(*clause, *a);true);
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
#[ensures(result === true ==> f.eventually_sat(*a))]
#[ensures(result === false ==> !f.eventually_sat_complete(*a))]
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
