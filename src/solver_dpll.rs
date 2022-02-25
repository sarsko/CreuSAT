use crate::lit::*;
use crate::clause::*;
use crate::assignments::*;
use crate::formula::*;

fn main() {}

pub fn is_clause_sat(f: &Formula, idx: usize, a: &Assignments) -> bool {
    let clause = &f.clauses[idx];
    let mut i: usize = 0;
    while i < clause.0.len() {
        let lit = clause.0[i];
        if lit.polarity as u8 == a.0[lit.idx] {
            return true;
        }
        i += 1;
    }
    return false;
}

pub fn is_clause_unsat(f: &Formula, idx: usize, a: &Assignments) -> bool {
    let clause = &f.clauses[idx];
    let mut i: usize = 0;
    while i < clause.0.len() {
        let lit = clause.0[i];
        if lit.polarity as u8 == a.0[lit.idx] {
            return false;
        } else if a.0[lit.idx] >= 2 {
            return false;
        }
        i += 1;
    }
    return true;
}

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

pub fn solver(f: &Formula) -> bool {
    // should do pure literal and identifying unit clauses in preproc
    if f.num_vars == 0 {
        return true;
    }
    let mut assignments = Assignments::new(f);
    inner(f, &mut assignments)
}

/// Takes a 1-indexed 2d vector and converts it to a 0-indexed formula
pub fn preproc_and_solve(
    clauses: &mut std::vec::Vec<std::vec::Vec<i32>>,
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
