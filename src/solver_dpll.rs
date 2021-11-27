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
use crate::predicates::*;

fn main() {}

#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[ensures((^a).invariant(*f))]
#[ensures(result === true ==> f.eventually_sat(*a))]
#[ensures(result === false ==> f.eventually_unsat(*a))]
fn inner(f: &Formula, a: &mut Assignments) -> bool {
    //a.do_unit_propagation(f);
    match f.eval(a) {
        SatState::Sat => return true,
        SatState::Unsat => return false,
        _ => {}
    };
    let mut a_cloned2 = a.clone();

    let next = a.find_unassigned();

    a_cloned2.assign(next, AssignedState::Positive, f);
    a.assign(next, AssignedState::Negative, f);

    if inner(f, a) {
        return true;
    } else {
        return inner(f, &mut a_cloned2);
    }
}
