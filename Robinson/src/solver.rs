extern crate creusot_contracts;
#[allow(unused)]
use creusot_contracts::std::*;
#[allow(unused)]
use creusot_contracts::*;

use crate::assignments::*;
use crate::decision::*;
use crate::formula::*;

pub enum SatResult {
    Sat(Vec<AssignedState>),
    Unsat,
    Unknown,
    Err,
}

#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(d.invariant(@f.num_vars))]
#[ensures(result == true ==> f.eventually_sat(a))]
#[ensures(result == false ==> !f.eventually_sat_complete(a))]
fn inner(f: &Formula, mut a: Assignments, d: &Decisions) -> bool {
    match a.do_unit_propagation(f) {
        Some(n) => {
            return n;
        }
        _ => {}
    }
    let next = a.find_unassigned(d, f);
    let mut a_cloned = a.clone();
    a.0[next] = 1;
    let old_a1 = a.1;
    if inner(f, a, d) {
        return true;
    }
    a_cloned.0[next] = 0;
    a_cloned.1 = old_a1;
    return inner(f, a_cloned, d);
}

#[cfg_attr(feature = "trust_solver", trusted)]
#[ensures(match result {
    SatResult::Sat(_assn) => { formula.eventually_sat_no_ass()
                               //formula.sat_inner(@assn) // TODO on returning satisfying assignment
    },
    SatResult::Unsat     => { !formula.eventually_sat_complete_no_ass() },
    _                    => { true },
})]
pub fn solver(formula: &mut Formula) -> SatResult {
    match formula.check_formula_invariant() {
        SatResult::Unknown => {}
        o => return o,
    }
    let assignments = Assignments::new(formula);
    let decisions = Decisions::new(formula);
    if inner(formula, assignments, &decisions) {
        return SatResult::Sat(Vec::new());
    }
    return SatResult::Unsat;
}
