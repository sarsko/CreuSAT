use std::collections::HashSet;

use crate::parser::parse_cnf;
use crate::types::*;

fn consistent(clauses: &Clauses) -> bool {
    let mut seen = HashSet::new();
    for clause in clauses {
        for literal in clause {
            if seen.contains(&-*literal) {
                return false;
            }
            seen.insert(literal);
        }
    }
    return true;
}

fn contains_empty(clauses: &Clauses) -> bool {
    for clause in clauses {
        if clause.len() == 0 {
            return true;
        }
    }
    return false;
}

fn unit_propagate(clauses: &Clauses, literal: Literal) -> Clauses {
    let mut out_clauses = vec![];
    for clause in clauses {
        if !clause.contains(&literal) {
            let mut out_clause = vec![];
            for lit in clause {
                if lit != &-literal {
                    out_clause.push(*lit);
                }
            }
            out_clauses.push(out_clause);
        }
    }
    return out_clauses;
}

fn pure_literal_assign(clauses: &Clauses, literal: Literal) -> Clauses {
    let mut out_clauses = vec![];
    for clause in clauses {
        if !clause.contains(&literal) {
            let mut out_clause = vec![];
            for lit in clause {
                out_clause.push(*lit);
            }
            out_clauses.push(out_clause);
        }
    }
    return out_clauses;
}

fn choose_literal(_clauses: &Clauses, clause_counter: i32) -> Literal {
    return clause_counter;
}

pub fn dpll(clauses: &mut Clauses, clause_counter: i32) -> bool {
    if contains_empty(clauses) {
        return false;
    }
    if consistent(clauses) {
        return true;
    }
    let mut stabilized = false;
    while !stabilized {
        stabilized = true;
        for i in 0..clauses.len() {
            if clauses[i].len() == 1 {
                *clauses = unit_propagate(&clauses, clauses[i][0]);
                stabilized = false;
                break;
            }
        }
    }
    let mut pures = vec![];
    let mut seen = HashSet::new();
    for i in 0..clauses.len() {
        for &literal in &clauses[i] {
            seen.insert(literal);
        }
    }
    for literal in &seen {
        if !seen.contains(&-*literal) {
            pures.push(*literal);
        }
    }
    for literal in pures {
        *clauses = pure_literal_assign(&clauses, literal);
    }
    let literal = choose_literal(&clauses, clause_counter);
    let new_counter = clause_counter + 1;
    let mut clauses1 = clauses.clone();
    clauses1.push(vec![literal]);
    let mut clauses2 = clauses.clone();
    clauses2.push(vec![-literal]);
    return dpll(&mut clauses1, new_counter) || dpll(&mut clauses2, new_counter);
}
