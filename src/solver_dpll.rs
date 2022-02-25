use crate::lit::*;
use crate::clause::*;
use crate::assignments::*;
use crate::formula::*;

fn main() {}

pub fn is_clause_sat(f: &Formula, idx: usize, a: &Assignments) -> bool {
    let clause = &f.clauses[idx];
    if clause.first.polarity as u8 == a.0[clause.first.idx] || clause.second.polarity as u8 == a.0[clause.second.idx] {
        return true;
    }
    let mut i: usize = 0;
    while i < clause.rest.len() {
        let lit = clause.rest[i];
        if lit.polarity as u8 == a.0[lit.idx] {
            return true;
        }
        i += 1;
    }
    return false;
}

pub fn is_clause_unsat(f: &Formula, idx: usize, a: &Assignments) -> bool {
    let clause = &f.clauses[idx];
    if clause.first.polarity as u8 != a.0[clause.first.idx] || clause.second.polarity as u8 != a.0[clause.second.idx] {
        return false;
    }
    let mut i: usize = 0;
    while i < clause.rest.len() {
        let lit = clause.rest[i];
        if lit.polarity as u8 != a.0[lit.idx] {
            return false;
        }
        i += 1;
    }
    return true;
}

fn inner(f: &Formula, a: &mut Assignments) -> bool {
    //a.do_unit_propagation(f);
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

pub fn solver(f: &Formula, units: &Vec<Lit>) -> bool {
    // should do pure literal and identifying unit clauses in preproc
    if f.num_vars == 0 {
        return true;
    }
    let mut assignments = Assignments::new(f);
    inner(f, &mut assignments)
}

