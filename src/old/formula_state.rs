#![feature(type_ascription)]

extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

pub struct Ghost<T>(*mut T)
where
    T: ?Sized;

impl<T> Model for Ghost<T> {
    type ModelTy = T;
    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        panic!()
    }
}

impl<T> Ghost<T> {
    #[trusted]
    #[ensures(@result === *a)]
    fn record(a: &T) -> Ghost<T> {
        panic!()
    }
}

#[derive(Clone, Copy)]
struct Lit {
    idx: usize,
    polarity: bool,
}
struct Clause(Vec<Lit>);
struct Assignments(Vec<AssignedState>);
struct Worklist(Vec<Lit>);

pub struct Formula {
    clauses: Vec<Clause>,
    num_vars: usize,
}

#[derive(Copy, Clone, Eq)]
pub enum SatState {
    Unknown,
    Sat,
    Unsat,
}

#[derive(Copy, Clone, Eq)]
pub enum AssignedState {
    Unset,
    Positive,
    Negative,
}

impl PartialEq for SatState {
    fn eq(&self, other: &Self) -> bool {
        return match (self, other) {
            (SatState::Unknown, SatState::Unknown) => true,
            (SatState::Sat, SatState::Sat) => true,
            (SatState::Unsat, SatState::Unsat) => true,
            _ => false,
        }
    }
}

impl PartialEq for AssignedState {
    fn eq(&self, other: &Self) -> bool {
        return match (self, other) {
            (AssignedState::Unset, AssignedState::Unset) => true,
            (AssignedState::Positive, AssignedState::Positive) => true,
            (AssignedState::Negative, AssignedState::Negative) => true,
            _ => false,
        }
    }
}
fn main() {}


#[predicate]
fn vars_in_range(n: Int, c: Clause) -> bool {
    pearlite! {
        forall<i: usize> 0usize <= i && @i < (@(c.0)).len() ==>
            (0 <= @((@(c.0))[@i]).idx &&
        @((@(c.0))[@i]).idx < n)
    }
}
#[predicate]
fn formula_invariant(f: Formula) -> bool {
    pearlite! {
        (forall<i: usize> 0usize <= i && @i < (@(f.clauses)).len() ==>
        vars_in_range(@(f.num_vars), ((@(f.clauses))[@i])))
    }
}

#[predicate]
fn assignments_invariant(f: Formula, a: Assignments) -> bool {
    pearlite! {
        @f.num_vars === (@a.0).len()
    }
}

/*
#[predicate]
fn not_sat_clause(a: Assignments, c: Clause) -> bool {
    pearlite! {
        (!sat_clause(a, c) && !unknown(a, c))
    }
}
*/

#[predicate]
fn not_sat_clause(a: Assignments, c: Clause) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < (@c.0).len() ==>
            match (@a.0)[@(@c.0)[i].idx] {
                AssignedState::Positive => !(@c.0)[i].polarity,
                AssignedState::Negative => (@c.0)[i].polarity,
                AssignedState::Unset => false,
            }

    }
}

// It is sat if at least one is equal
#[predicate]
fn sat_clause(a: Assignments, c: Clause) -> bool {
    pearlite! {
        exists<i: Int> 0 <= i && i < (@c.0).len() &&
            match (@a.0)[@(@c.0)[i].idx] {
                AssignedState::Positive => (@c.0)[i].polarity,
                AssignedState::Negative => !(@c.0)[i].polarity,
                AssignedState::Unset => !(@c.0)[i].polarity && (@c.0)[i].polarity
            }
    }
}

// It is unknown if there exists a None, and all the clauses that are some have the wrong polarity
#[predicate]
fn unknown(a: Assignments, c: Clause) -> bool {
    pearlite! {
        (exists<i: Int> 0 <= i && i < (@c.0).len() &&
            match (@a.0)[@(@c.0)[i].idx] {
                AssignedState::Positive => false,
                AssignedState::Negative => false,
                AssignedState::Unset => true
            }
        )
        &&
        (forall<i: Int> 0 <= i && i < (@c.0).len() ==>
            match (@a.0)[@(@c.0)[i].idx] {
                AssignedState::Positive => (@c.0)[i].polarity,
                AssignedState::Negative => !(@c.0)[i].polarity,
                AssignedState::Unset => true
            })
    }
}

#[predicate]
fn unknown2(a: Assignments, c: Clause) -> bool {
    pearlite! {
        !sat_clause(a,c) && !not_sat_clause(a, c)
    }
}

#[predicate]
fn sat_formula(a: Assignments, f: Formula) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < (@(f.clauses)).len() ==>
        sat_clause(a, (@(f.clauses))[i])
    }
}

#[predicate]
fn not_sat_formula(a: Assignments, f: Formula) -> bool {
    pearlite! {
        exists<i: Int> 0 <= i && i < (@(f.clauses)).len() &&
        not_sat_clause(a, (@(f.clauses))[i])
    }
}

#[trusted]
#[ensures(result === true ==> (l === r))]
#[ensures(result === false ==> (l != r))]
#[ensures(result === (l === r))]
fn eqb(l: bool, r: bool) -> bool {
    l == r
}

#[logic]
fn eqUnsat(l: SatState) -> bool {
    pearlite!{
        match l {
            SatState::Unsat => true,
            _ => false
        }
    }
}

#[logic]
fn eqSat(l: SatState) -> bool {
    pearlite!{
        match l {
            SatState::Sat => true,
            _ => false
        }
    }
}

#[logic]
fn eqUnknown(l: SatState) -> bool {
    pearlite!{
        match l {
            SatState::Unknown => true,
            _ => false
        }
    }
}


#[ensures(result  ===  sat_clause(*a, (@f.clauses)[@idx]))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[requires(@idx < (@f.clauses).len())]
fn is_clause_sat(f: &Formula, idx: usize, a: &Assignments) -> bool {
    let clause = &f.clauses[idx];
    let mut i = 0;
    #[invariant(previous, forall<j: Int> 0 <= j && j < @i ==>
        match (@a.0)[@(@clause.0)[j].idx] {
            AssignedState::Positive => !(@clause.0)[j].polarity,
            AssignedState::Negative => (@clause.0)[j].polarity,
            AssignedState::Unset => true,
        }
    )]
    while i < clause.0.len() {
        let lit = clause.0[i];
        match a.0[lit.idx]{
           AssignedState::Positive => {
                if lit.polarity {
                    return true
                }
            },
            AssignedState::Negative => {
                if !lit.polarity {
                    return true
                }
            },
            AssignedState::Unset => {
            }
        }
        i += 1;
    }
    return false;
}

/*
#[ensures(result  ==> not_sat_clause(*a, (@f.clauses)[@idx]))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[requires(@idx < (@f.clauses).len())]
fn is_clause_unsat(f: &Formula, idx: usize, a: &Assignments) -> bool {
    let unknown = is_clause_unknown(f, idx, a);
    let sat = is_clause_sat(f, idx, a);
    return !unknown && !sat;
}
*/

#[ensures(result  === not_sat_clause(*a, (@f.clauses)[@idx]))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[requires(@idx < (@f.clauses).len())]
fn is_clause_unsat(f: &Formula, idx: usize, a: &Assignments) -> bool {
    let clause = &f.clauses[idx];
    let mut i = 0;
    let mut unassigned = 0;
    #[invariant(loop_invariant, 0usize <= i && @i <= (@clause.0).len())]
    #[invariant(unass, unassigned <= i)]
    #[invariant(previous, forall<j: Int> 0 <= j && j < @i ==>
        match (@a.0)[@(@clause.0)[j].idx] {
            AssignedState::Positive => !(@clause.0)[j].polarity,
            AssignedState::Negative => (@clause.0)[j].polarity,
            AssignedState::Unset => false,
        }
    )]
    while i < clause.0.len() {
        let lit = clause.0[i];
        match a.0[lit.idx]{
           AssignedState::Positive => {
                if lit.polarity {
                    return false
                }
            },
            AssignedState::Negative => {
                if !lit.polarity {
                    return false
                }
            },
            AssignedState::Unset => {
                return false;
            }
        }
        i += 1;
    }
    return true;
}

#[ensures(result === unknown2(*a, (@f.clauses)[@idx]))]
#[ensures(result === false  ==> (not_sat_clause(*a, (@f.clauses)[@idx]) || sat_clause(*a, (@f.clauses)[@idx])))]
#[ensures(result === true  ==> (!not_sat_clause(*a, (@f.clauses)[@idx]) && !sat_clause(*a, (@f.clauses)[@idx])))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[requires(@idx < (@f.clauses).len())]
#[requires((@f.clauses).len() > 0)]
fn is_clause_unknown2(f: &Formula, idx: usize, a: &Assignments) -> bool {
    if is_clause_sat(f, idx, a) || is_clause_unsat(f, idx, a) {
        return false;
    } else {
        return true;
    }
}

//#[ensures(result === unknown2(*a, (@f.clauses)[@idx]))]
#[ensures(result === SatState::Unsat  ==> not_sat_clause(*a, (@f.clauses)[@idx]))]
#[ensures(result === SatState::Sat  ==> sat_clause(*a, (@f.clauses)[@idx]))]
#[ensures(result === SatState::Unknown  ==> (!not_sat_clause(*a, (@f.clauses)[@idx]) && !sat_clause(*a, (@f.clauses)[@idx])))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[requires(@idx < (@f.clauses).len())]
#[requires((@f.clauses).len() > 0)]
fn get_clause_state(f: &Formula, idx: usize, a: &Assignments) -> SatState {
    if is_clause_sat(f, idx, a) {
        return SatState::Sat;
    } else if is_clause_unsat(f, idx, a) {
        return SatState::Unsat;
    } else {
        return SatState::Unknown;
    }
}

/*
#[ensures(result  ==> unknown(*a, (@f.clauses)[@idx]))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[requires(@idx < (@f.clauses).len())]
#[requires((@f.clauses).len() > 0)]
fn is_clause_unknown(f: &Formula, idx: usize, a: &Assignments) -> bool {
    let clause = &f.clauses[idx];
    let mut i = 0;
    let mut unassigned = false;
    #[invariant(loop_invariant, 0usize <= i && @i <= (@clause.0).len())]
    #[invariant(previous, forall<j: Int> 0 <= j && j < @i ==>
        match (@a.0)[@(@clause.0)[j].idx] {
            AssignedState::Positive => !(@clause.0)[j].polarity,
            AssignedState::Negative => (@clause.0)[j].polarity,
            AssignedState::Unset => true
        }
    )]
    while i < clause.0.len() {
        let lit = clause.0[i];
        match a.0[lit.idx]{
           AssignedState::Positive => {
                if eqb(lit.polarity, true)  {
                    return false
                }
            },
            AssignedState::Negative => {
                if eqb(lit.polarity, false)  {
                    return false
                }
            },
            AssignedState::Unset => {
                unassigned = true;
            }
        }
        i += 1;
    }
    if unassigned {
        return true;
    }
    else {
        return false;
    }
}
*/

#[trusted]
#[ensures(result === SatState::Sat     ==>  sat_clause(*a, (@f.clauses)[@idx]))]
#[ensures(result === SatState::Unknown ==> unknown(*a, (@f.clauses)[@idx]))]
#[ensures(result === SatState::Unsat   ==>  not_sat_clause(*a, (@f.clauses)[@idx]))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[requires(@idx < (@f.clauses).len())]
fn get_clause_state_old(f: &Formula, idx: usize, a: &Assignments) -> SatState {
    let clause = &f.clauses[idx];
    let mut i = 0;
    let mut unknown = 0;
    #[invariant(loop_invariant, 0usize <= i && @i <= (@clause.0).len())]
    #[invariant(uno, unknown <= i)]
    while i < clause.0.len() {
        let lit = clause.0[i];
        match a.0[lit.idx]{
           AssignedState::Positive => {
                if eqb(lit.polarity, true)  {
                    return SatState::Sat;
                }
            },
            AssignedState::Negative => {
                if eqb(lit.polarity, false)  {
                    return SatState::Sat;
                }
            },
            AssignedState::Unset => {
                unknown += 1;
            }
        }
        i += 1;
    }
    if unknown > 0 {
        return SatState::Unknown;
    }
    else {
        return SatState::Unsat;
    }
}

#[trusted]
#[ensures(result === SatState::Sat   ==>  sat_formula(*a, *f))]
#[ensures(result === SatState::Unsat ==> not_sat_formula(*a, *f))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
fn get_formula_state(f: &Formula, a: &Assignments) -> SatState {
    let mut i = 0;
    let mut outState = SatState::Sat;
    #[invariant(prev,
        forall<k: Int> 0 <= k && k < @i ==>
        !(not_sat_clause(*a, (@f.clauses)[k])))]
    #[invariant(loop_invariant, 0usize <= i && @i <= (@f.clauses).len())]
    while i < f.clauses.len() {
        let res = get_clause_state(f, i, a);
        match res {
            SatState::Unsat => return SatState::Unsat,
            SatState::Unknown => outState = SatState::Unknown,
            SatState::Sat => {},
        }
        i += 1
    }
    return outState;
}



#[ensures(result === true ==> not_sat_formula(*a, *f))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
fn is_formula_unsat(f: &Formula, a: &Assignments) -> bool {
    let mut i = 0;
    #[invariant(prev,
        forall<k: Int> 0 <= k && k < @i ==>
        not_sat_clause(*a, (@f.clauses)[k]))]
    #[invariant(loop_invariant, 0usize <= i && @i <= (@f.clauses).len())]
    while i < f.clauses.len() {
        if is_clause_unsat(f, i, a) {
            return true;
        }
    }
    return false;
}
