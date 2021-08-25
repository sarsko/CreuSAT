use std::collections::HashSet;

use crate::types::*;

fn consistent(clauses: &Clauses) -> bool {
    let mut seen = HashSet::new();
    let mut i = 0;
    let clauses_len = clauses.len();
    while i < clauses_len {
        let mut j = 0;
        let clause = &clauses[i];
        let clause_len = clause.len();
        while j < clause_len {
            let literal = &clause[j];
            if seen.contains(&-*literal) {
                return false;
            }
            seen.insert(literal);
            j += 1;
        }
        i += 1;
    }
    return true;
}

fn contains_empty(clauses: &Clauses) -> bool {
    let mut i = 0;
    let clauses_len = clauses.len();
    while i < clauses_len {
        let clause = &clauses[i];
        if clause.len() == 0 {
            return true;
        }
        i += 1;
    }
    return false;
}

fn unit_propagate(clauses: &Clauses, literal: Literal) -> Clauses {
    let mut out_clauses = vec![];
    let mut i = 0;
    let clauses_len = clauses.len();
    while i < clauses_len {
        let clause = &clauses[i];
        if !clause.contains(&literal) {
            let mut out_clause = vec![];
            let mut j = 0;
            let clause_len = clause.len();
            while j < clause_len {
                let lit = &clause[j];
                if lit != &-literal {
                    out_clause.push(*lit);
                }
                j += 1;
            }
            out_clauses.push(out_clause);
        }
        i += 1;
    }
    return out_clauses;
}

fn pure_literal_assign(clauses: &Clauses, literal: Literal) -> Clauses {
    let mut out_clauses = vec![];
    let mut i = 0;
    let clauses_len = clauses.len();
    while i < clauses_len {
        let clause = &clauses[i];
        if !clause.contains(&literal) {
            let mut out_clause = vec![];
            let mut j = 0;
            let clause_len = clause.len();
            while j < clause_len {
                let lit = &clause[j];
                out_clause.push(*lit);
                j += 1;
            }
            out_clauses.push(out_clause);
        }
        i += 1;
    }
    return out_clauses;
}

fn choose_literal(_clauses: &Clauses, clause_counter: i32) -> Literal {
    return clause_counter;
}

pub fn dpll(clauses: &mut Clauses, clause_counter: i32) -> bool {
    let mut i;
    if contains_empty(clauses) {
        return false;
    }
    if consistent(clauses) {
        return true;
    }
    let mut stabilized = false;
    while !stabilized {
        stabilized = true;
        i = 0;
        let clauses_len = clauses.len();
        while i < clauses_len {
            if clauses[i].len() == 1 {
                *clauses = unit_propagate(&clauses, clauses[i][0]);
                stabilized = false;
                break;
            }
            i += 1;
        }
    }
    let mut pures = vec![];
    let mut seen = HashSet::new();
    i = 0;
    let clauses_len = clauses.len();
    while i < clauses_len {
        let mut j = 0;
        let clause = &clauses[i];
        let clause_len = clause.len();
        while j < clause_len {
            let literal = &clause[j];
            seen.insert(*literal);
            j += 1;
        }
        i += 1;
    }
    for literal in &seen {
        if !seen.contains(&-*literal) {
            pures.push(*literal);
        }
    }
    i = 0;
    let pures_len = pures.len();
    while i < pures_len {
        let literal = pures[i];
        *clauses = pure_literal_assign(&clauses, literal);
        i += 1;
    }
    let literal = choose_literal(&clauses, clause_counter);
    let new_counter = clause_counter + 1;
    let mut clauses2 = clauses.clone();
    let mut clauses = clauses;
    clauses.push(vec![literal]);
    clauses2.push(vec![-literal]);
    return dpll(&mut clauses, new_counter) || dpll(&mut clauses2, new_counter);
}
