extern crate creusot_contracts;
use creusot_contracts::*;

use crate::{assignments::*, decision::*, formula::*};

pub enum SatResult {
    Sat(Vec<AssignedState>),
    Unsat,
    Unknown,
}

#[requires(f.inv())]
#[requires(a.inv(*f))]
#[requires(d.inv(f.num_vars@))]
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
#[requires(forall<i: Int> 0 <= i && i < formula.clauses@.len() ==>
        formula.clauses@[i].vars_in_range(usize::MAX@))]
#[ensures(match result {
    SatResult::Sat(_assn) => { (^formula).eventually_sat_no_ass()
                               //&& formula.sat_inner(assn@) // TODO on returning satisfying assignment
    },
    SatResult::Unsat     => { !(^formula).eventually_sat_complete_no_ass() },
    _                    => { false }, // We are complete
})]
#[ensures((^formula).clauses == formula.clauses)]
pub fn solver(formula: &mut Formula) -> SatResult {
    let old_f: Snapshot<&mut Formula> = snapshot!(formula);
    match formula.check_and_establish_formula_invariant() {
        SatResult::Unknown => {}
        o => return o,
    }
    proof_assert!(formula.clauses == old_f.clauses);
    let assignments = Assignments::new(formula);
    let decisions = Decisions::new(formula);
    if inner(formula, assignments, &decisions) {
        return SatResult::Sat(Vec::new());
    }
    return SatResult::Unsat;
}
