use std::collections::HashSet;

use crate::types::*;

use std::marker;

struct CVec<T> {
    data: *const T, // *const for variance!
    len: usize,
    cap: usize,
    _marker: marker::PhantomData<T>,
}

// This is a WIP with pseudocode all over

// Invariants for all the loops
// Ensures for all the functions
// Requires somewhere probably

/// Returns `true` if no literal has both positive and negative polarity, and
/// `false` if there exists at least one literal with both polarities

// Split into one function which extracts all literals to a set and then another
// Function which checks if the set contains both a literal and its negation?
// Would need to save length of clauses then, but may have to do that anyways
// If so, first function would iterate over all clauses and add all literals and
// thus ensure that all literals are in the returned set
// And the second would iterate over all positive literals and check if the negation
// exists

// Need to modularize/rewrite this function?
/*
#[requires(false)]
#[ensures(forall literals ... ==> result == false &&
    forall literals ... ==> result == true)]
*/
fn consistent(clauses: &Clauses) -> bool {
    let mut seen = HashSet::new();
    let mut i = 0;
    let clauses_len = clauses.len();
    // For all the clauses
//    #[invariant(loop_bound, i <= clauses_len)]
    while i < clauses_len {
        let mut j = 0;
        let clause = &clauses[i];
        let clause_len = clause.len();
        // For all the literals
//        #[invariant(loop_bound, j <= clause_len)]
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
        i += 1;
    }
    return true;
}

// #[ensures(result == true if exists a clause with len 0)]
// or
// #[ensures(result == false if forall clause len(clause) > 0)]
// or something like that

/// Returns `true` if there exists an empty clause, and `false` otherwise

// Will need a small rewrite, but the structure should be OK
/*
#[requires(false)]
#[ensures(!(forall<i:Int> 0 <= i && i < clauses_len &&
    len(get(i)) >  0) ==> result === true)
    forall<i:Int> 0 <= i && i < clauses_len &&
    len(get(i)) >  0 ==> result === true)]
*/
fn contains_empty(clauses: &Clauses) -> bool {
    let mut i = 0;
    let clauses_len = clauses.len();
    // For all the clauses
//    #[invariant(loop_bound, i <= clauses_len)]
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

/// Takes the clauses and a literal which occurs as a unit clause(only one literal
/// in the clause -> value is "forced"), and returns a new set of clauses where
/// each clause containing the literal is removed, and where each negation of the
/// literal is removed.
/*
#[requires(false)] // May require that the clauses contain literal & are well formed
#[ensures(result.contains(literal) === false)]
#[ensures(result.contains(-literal) === false)]
#[ensures(len(result) < len(clauses))]
*/
fn unit_propagate(clauses: &Clauses, literal: Literal) -> Clauses {
    let mut out_clauses = vec![];
    let mut i = 0;
    let clauses_len = clauses.len();
 //   #[invariant(loop_bound, i <= clauses_len)]
    while i < clauses_len {
        let clause = &clauses[i];
        if !clause.contains(&literal) {
            let mut out_clause = vec![];
            let mut j = 0;
            let clause_len = clause.len();
 //           #[invariant(loop_bound, j <= clause_len)]
            while j < clause_len {
                let lit = clause[j];
                if lit != -literal {
                    out_clause.push(lit);
                }
                j += 1;
            }
            out_clauses.push(out_clause);
        }
        i += 1;
    }
    return out_clauses;
}

// #[ensures(result.contains(literal) == false)
// #[ensures(result.contains(-literal) == false) // not strictly derivable? Get from UP?
// Ensures result.len() < clauses.len ?

/// Takes the clauses and a literal which occurs pure(only one polarity) in the
/// formula, and returns a new set of clauses where each clause containing the
/// literal is removed.
/*
#[requires(false)] // May require that the clauses contain literal
#[ensures(result.contains(literal) == false)]
#[ensures(result.contains(-literal) == false)]
#[ensures(len(result) < len(clauses))]
*/
fn pure_literal_assign(clauses: &Clauses, literal: Literal) -> Clauses {
    let mut out_clauses = vec![];
    let mut i = 0;
    let clauses_len = clauses.len();
//    #[invariant(loop_bound, i <= clauses_len)]
    while i < clauses_len {
        let clause = &clauses[i];
        if !clause.contains(&literal) {
            let mut out_clause = vec![];
            let mut j = 0;
            let clause_len = clause.len();
//            #[invariant(loop_bound, j <= clause_len)]
            while j < clause_len {
                let lit = clause[j];
                out_clause.push(lit);
                j += 1;
            }
            out_clauses.push(out_clause);
        }
        i += 1;
    }
    return out_clauses;
}

// Probably gonna need some variant that the chosen literal sooner or later
// reaches `num_literals` though that is enforced by `dpll`

/// Naively returns the clause_counter directly -> requires the counter to be
/// changed elsewhere

// May be changed to increment -> eventually all literals will be chosen
fn choose_literal(_clauses: &Clauses, clause_counter: i32) -> Literal {
    return clause_counter;
}

/// Takes a set of clauses and returns `true` in the case that the clauses are
/// satisfiable, and `false` in the case that the clauses are not satisfiable
/*
#[requires(false)] // requires some well-formedness?
#[ensures(... ==> result == false &&
    ... ==> result == true)]
*/
pub fn dpll(clauses: &mut Clauses, clause_counter: i32, num_literals: usize) -> bool {
    let mut i;
    // If there is an empty clause then that clause is not satisfiable and thus
    // the entire formula is not satisfiable
    if contains_empty(clauses) {
        return false;
    }
    // If no literal occurs with both polarities, then the formula is satisfiable
    if consistent(clauses) {
        return true;
    }
    let mut stabilized = false;
    // Gonna need something here?
    while !stabilized {
        stabilized = true;
        i = 0;
        let clauses_len = clauses.len();
//        #[invariant(loop_bound, i <= clauses_len)]
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
    let mut seen_vec = vec![];
    i = 0;
    let clauses_len = clauses.len();
//    #[invariant(loop_bound, i <= clauses_len)]
    while i < clauses_len {
        let mut j = 0;
        let clause = &clauses[i];
        let clause_len = clause.len();
//        #[invariant(loop_bound, j <= clause_len)]
        while j < clause_len {
            let literal = clause[j];
            if !seen.contains(&literal) {
                seen_vec.push(literal);
                seen.insert(literal);
            }
            j += 1;
        }
        i += 1;
    }
    i = 0;
    let seen_vec_len = seen_vec.len();
//    #[invariant(loop_bound, i <= seen_vec_len)]
    while i < seen_vec_len {
        let literal = seen_vec[i];
        if !seen.contains(&-literal) {
            pures.push(literal);
        }
        i += 1;
    }
    i = 0;
    let pures_len = pures.len();
//    #[invariant(loop_bound, i <= pures_len)]
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
    return dpll(&mut clauses, new_counter, num_literals) || dpll(&mut clauses2, new_counter, num_literals);
}
