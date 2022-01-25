#![feature(type_ascription)]

extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;
use crate::ghost;
use crate::lit::*;
use crate::clause::*;
use crate::assignments::*;
use crate::formula::*;
use crate::logic::*;

fn main() {}

#[logic]
// Duplis from lemma_decreases_numof
#[requires(t.len() === t2.len())]
#[requires(0 <= i && i < t.len())]
#[requires(t[i] === v && !(t2[i] === v))]
#[requires(forall<j: Int> 0 <= i && i < t.len() ==> j != i ==> t[j] === t2[j])]

#[variant(t.len() - j)]
#[requires(0 <= j && j <= t.len())]
#[ensures(result === occ(v, t, j, t.len()))]
#[ensures( (j <= i) ==> occ(v, t2, j, t2.len()) === (result - 1))]
#[ensures( (j > i) ==> occ(v, t2, j, t2.len()) === result)]
fn numof_aux(v: Option<bool>, t: Seq<Option<bool>>, t2: Seq<Option<bool>>, i: Int, j: Int) -> Int {
    if pearlite! { j === t.len() } {
        0
    } else if pearlite! { j === i } {
        numof_aux(v, t, t2, i, j+1) + 1
    } else if pearlite! { t[j] === v } {
        numof_aux(v, t, t2, i, j+1) + 1
    } else {
        numof_aux(v, t, t2, i, j+1)
    }
}

#[logic]
#[requires(t.len() === t2.len())]
#[requires(0 <= i && i < t.len())]
#[requires(t[i] === v && !(t2[i] === v))]
#[requires(forall<j: Int> 0 <= i && i < t.len() ==> j != i ==> t[j] === t2[j])]
#[ensures(occ(v, t2, 0, t2.len()) === occ(v, t, 0, t.len()) - 1)]
fn lemma_decreases_numof(v: Option<bool>, t: Seq<Option<bool>>, t2: Seq<Option<bool>>, i: Int) {
    pearlite! { numof_aux(v, t, t2, i, 0) };
}

#[ensures(result === (@f.clauses)[@idx].sat(*a))]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(@idx < (@f.clauses).len())]
pub fn is_clause_sat(f: &Formula, idx: usize, a: &Assignments) -> bool {
    let clause = &f.clauses[idx];
    let mut i: usize = 0;
    #[invariant(previous, forall<j: Int> 0 <= j && j < @i ==>
        match (@a)[@(@clause)[j].idx] {
            AssignedState::Positive => !(@clause)[j].polarity,
            AssignedState::Negative => (@clause)[j].polarity,
            AssignedState::Unset => true,
        }
    )]
    while i < clause.0.len() {
        let lit = clause.0[i];
        match a.0[lit.idx]{
           AssignedState::Positive => {
                if lit.polarity {
                    return true
                }
            },
            AssignedState::Negative => {
                if !lit.polarity {
                    return true
                }
            },
            AssignedState::Unset => {
            }
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
    #[invariant(loop_invariant, 0 <= @i && @i <= (@clause).len())]
    #[invariant(previous, forall<j: Int> 0 <= j && j < @i ==>
        match (@a)[@(@clause)[j].idx] {
            AssignedState::Positive => !(@clause)[j].polarity,
            AssignedState::Negative => (@clause)[j].polarity,
            AssignedState::Unset => false,
        }
    )]
    while i < clause.0.len() {
        let lit = clause.0[i];
        match a.0[lit.idx]{
           AssignedState::Positive => {
                if lit.polarity {
                    return false
                }
            },
            AssignedState::Negative => {
                if !lit.polarity {
                    return false
                }
            },
            AssignedState::Unset => {
                return false;
            }
        }
        i += 1;
    }
    return true;
}

#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[ensures((^a).invariant(*f))]
#[ensures(result === true ==> f.eventually_sat(*a))]
#[ensures(result === false ==> f.eventually_unsat(*a))]
fn inner(f: &Formula, a: &mut Assignments) -> bool {
    a.do_unit_propagation(f);
    match f.eval(a) {
        SatState::Sat => return true,
        SatState::Unsat => return false,
        _ => {}
    };
    let mut a_cloned = a.clone();
    let mut a_cloned2 = a.clone();

    let next = a.find_unassigned();

    a_cloned2.assign(next, AssignedState::Positive, f);
    a_cloned.assign(next, AssignedState::Negative, f);
    //a_cloned.0[next] = AssignedState::Positive;
    //a_cloned2.0[next] = AssignedState::Negative;

    /*
    proof_assert! { { lemma_eventually_assigned(@a, 0, *f); true }}
    proof_assert! { { lemma_eventually_assigned(@a, @next, *f); true }}
    proof_assert! { a.compatible(a_cloned) };
    proof_assert! { a.compatible(a_cloned2) };
    */

    if inner(f, &mut a_cloned) {
        return true;
    } else {
        return inner(f, &mut a_cloned2);
    }
}
