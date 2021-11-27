extern crate creusot_contracts;

use std::vec as rvec;
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

#[trusted] // TMP, PASSES
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

#[trusted]
pub fn preproc_and_solve(
    clauses: &mut rvec::Vec<rvec::Vec<i32>>,
    num_literals: usize,
) -> bool {
    let mut formula = Formula {
        clauses: Vec::new(),
        num_vars: num_literals,
    };
    for clause in clauses {
        let mut currclause = Clause(Vec::new());
        for lit in clause {
            if *lit < 0 {
                let new_lit = Lit {
                    idx: ((lit.abs() - 1) as usize),
                    polarity: false,
                };
                currclause.0.push(new_lit);
            } else {
                let new_lit = Lit {
                    idx: ((*lit - 1) as usize),
                    polarity: true,
                };
                currclause.0.push(new_lit);
            }
        }
        formula.clauses.push(currclause);
    }
    return solver(&formula);
}

#[trusted] // TMP, PASSES
#[requires(f.invariant())]
//#[ensures(result === true ==> f.eventually_sat(*a))]
//#[ensures(result === false ==> f.eventually_unsat(*a))]
pub fn solver(f: &Formula) -> bool {
    // should do pure literal and identifying unit clauses in preproc
    if f.num_vars == 0 {
        return true;
    }
    let mut assignments = Assignments::new(f);
    inner(f, &mut assignments)
}