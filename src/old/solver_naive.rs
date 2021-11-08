use std::collections::HashSet;

use crate::types::*;

//#[requires(false)]
#[ensures(result === clause_counter)]
fn choose_literal(_clauses: &Clauses, clause_counter: i32) -> Literal {
    return clause_counter;
}

#[requires(false)]
// How to ensure the opposite?
#[ensures(exists<i:Int> 0 <= i && i < clauses_len &&
    len(get(i)) == 0 ==> result === true)]
fn contains_empty(clauses: &Clauses) -> bool {
    let mut i = 0;
    let clauses_len = clauses.len();
    // For all the clauses
    #[invariant(loop_bound, i <= clauses_len)]
    while i < clauses_len {
        // Get the clause. If the length is 0, return `true`
        let clause = &clauses[i];
        if clause.len() == 0 {
            return true;
        }
        i += 1;
    }
    return false;
}

// How to ensure the opposite?
#[ensures(exists<i:Int> 0 <= i && i < clause_len &&
    seen.contains(&-i) ==> result === false)]
#[ensures(len(seen) <= len(^seen))]
fn consistent_check_clause(clause: &Clause, seen: &mut HashSet<Clause>) -> bang {
    let mut j = 0;
    let clause_len = clause.len();
    // For all the literals
    #[invariant(loop_bound, j <= clause_len)]
    while j < clause_len {
        let literal = clause[j];
        // If we have already seen the negation -> return false
        if seen.contains(&-literal) {
            return false;
        }
        // Add this to seen
        seen.insert(literal);
        j += 1;
    }
    return true;
}

#[requires(false)]
// Again, the opposite
#[ensures(exists<i:Int> 0 <= i && i < clauses_len &&
    consistent_check_clause(&clauses[i], &mut seen) ===> result == false)]
fn consistent(clauses: &Clauses) -> bool {
    let mut seen: HashSet<Clause> = HashSet::new();
    let mut i = 0;
    let clauses_len = clauses.len();
    // For all the clauses
    #[invariant(loop_bound, i <= clauses_len)]
    while i < clauses_len {
        let clause = &clauses[i];
        if !consistent_check_clause(clause, &mut seen) {
            return false;
        }
        i += 1;
    }
    return true;
}

// Ensure that the result doesnt contain literal somehow
#[ensures(len(result) <= len(clauses))]
fn set_literals(clauses: Clauses, literal: Literal) -> Clauses {
    let mut out_clauses = vec![];
    let mut i = 0;
    let clauses_len = clauses.len();
    #[invariant(loop_bound, i <= clauses_len)]
    while i < clauses_len {
        let clause = &clauses[i];
        if !clause.contains(&literal) {
            out_clauses.push(clause.clone());
        }
        i += 1;
    }
    return out_clauses;
}

/// Takes a set of clauses and returns `true` in the case that the clauses are
/// satisfiable, and `false` in the case that the clauses are not satisfiable
#[requires(clause_counter <= num_literals)] // requires some well-formedness?
#[ensures(... ==> result === false &&
    ... ==> result === true)]
pub fn brute_force(clauses: &mut Clauses, clause_counter: i32, num_literals: usize) -> bool {
    // If there is an empty clause then that clause is not satisfiable and thus
    // the entire formula is not satisfiable
    if contains_empty(clauses) {
        return false;
    }
    // If no literal occurs with both polarities, then the formula is satisfiable
    if consistent(clauses) {
        return true;
    }
    let literal = choose_literal(&clauses, clause_counter);
    let new_counter = clause_counter + 1;
    let mut clauses = set_literals(clauses, literal);
    let mut clauses2 = set_literals(clauses, literal);
    set_literals(&mut clauses2, -literal);
    return dpll(&mut clauses, new_counter, num_literals) || dpll(&mut clauses2, new_counter, num_literals);
}
