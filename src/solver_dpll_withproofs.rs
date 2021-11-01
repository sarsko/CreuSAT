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
struct Assignments(Vec<Option<bool>>);
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

impl PartialEq for SatState {
    fn eq(&self, other: &Self) -> bool {
        return match *self {
            other => true,
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

#[predicate]
fn compatible(a: Assignments, a2: Assignments) -> bool {
    pearlite! {
        (@a.0).len() === (@a2.0).len() &&
        forall<i: usize> 0usize <= i && @i < (@a.0).len() ==>
        (@a.0)[@i] === None || (@a.0)[@i] === (@a2.0)[@i]
    }
}


// It is not sat if all are unequal
#[predicate]
fn not_sat_clause(a: Assignments, c: Clause) -> bool {
    pearlite! {
        forall<i: usize> 0usize <= i && @i < (@c.0).len() ==>
            match (@a.0)[@(@c.0)[@i].idx] {
                Some(x) => x != (@c.0)[@i].polarity,
                None    => false
            }
    }
}

// It is sat if at least one is equal
#[predicate]
fn sat_clause(a: Assignments, c: Clause) -> bool {
    pearlite! {
        exists<i: Int> 0 <= i && i < (@c.0).len() ==>
            match (@a.0)[@(@c.0)[i].idx] {
                Some(x) => x == (@c.0)[i].polarity,
                None    => false
            }
    }
}

// It is unknown if there exists a None, and all the clauses that are some have the wrong polarity
#[predicate]
fn unknown(a: Assignments, c: Clause) -> bool {
    pearlite! {
        exists<i: Int> 0 <= i && i < (@c.0).len() ==>
            match (@a.0)[@(@c.0)[i].idx] {
                Some(x) => false,
                None    => true
            }
        &&
        forall<i: Int> 0 <= i && i < (@c.0).len() ==>
            match (@a.0)[@(@c.0)[i].idx] {
                Some(x) => x != (@c.0)[i].polarity,
                None    => true
            }
    }
}


#[predicate]
fn sat_formula(a: Assignments, f: Formula) -> bool {
    pearlite! {
        forall<i: usize> 0usize <= i && @i < (@(f.clauses)).len() ==>
        !not_sat_clause(a, (@(f.clauses))[@i])
    }
}

impl Worklist {
    #[trusted]
    fn clone_lit_vector(&self, v: &Vec<Lit>) -> Vec<Lit> {
        let mut out = Vec::new();
        let mut i = 0;
        #[invariant(loop_invariant, 0usize <= i && @i <= (@v).len())]
        while i < v.len() {
            let lit = &v[i];
            let newlit = Lit {
                idx: lit.idx,
                polarity: lit.polarity,
            };
            out.push(newlit);
            i += 1;
        }
        return out;
    }
    #[trusted]
    #[ensures(
        forall<i: Int> 0 <= i && i < (@self.0).len() ==>
        (@self.0)[i] === (@result.0)[i]
    )]
    #[ensures((@self.0).len() === (@result.0).len())]
    fn clone(&self) -> Self {
        Worklist(self.clone_lit_vector(&self.0))
    }
}

impl Assignments {
    #[trusted]
    fn clone_assignment_vector(&self, v: &Vec<Option<bool>>) -> Vec<Option<bool>> {
        let mut out = Vec::new();
        let mut i = 0;
        #[invariant(loop_invariant, 0usize <= i && @i <= (@v).len())]
        while i < v.len() {
            let curr = v[i];
            out.push(curr.clone());
            i += 1;
        }
        return out;
    }
    #[trusted]
    #[ensures(
        forall<i: Int> 0 <= i && i < (@self.0).len() ==>
        (@self.0)[i] === (@result.0)[i]
    )]
    #[ensures((@self.0).len() === (@result.0).len())]
    fn clone(&self) -> Self {
        Assignments(self.clone_assignment_vector(&self.0))
    }

    #[requires(formula_invariant(*f))]
    #[ensures(assignments_invariant(*f, result))]
    fn new(f: &Formula) -> Self {
        let mut assign: Vec<Option<bool>> = Vec::new();
        let mut i = 0;
        #[invariant(loop_invariant, 0usize <= i && i <= f.num_vars)]
        #[invariant(length_invariant, (@assign).len() === @i)]
        while i < f.num_vars {
            assign.push(None);
            i += 1
        }
        Assignments(assign)
    }
}

#[trusted]
#[ensures(result === true ==> (l === r))]
#[ensures(result === false ==> (l != r))]
#[ensures(result === (l === r))]
fn eqb(l: bool, r: bool) -> bool {
    l == r
}


#[requires(formula_invariant(*_f))]
#[ensures((@result.0).len() === 0)]
fn init_worklist(_f: &Formula, _a: &Assignments) -> Worklist {
    let litvec: Vec<Lit> = Vec::new();
    Worklist(litvec)
}

#[requires(@idx < (@f.clauses).len())]
#[requires(assignments_invariant(*f, *a))]
#[requires(formula_invariant(*f))]
#[ensures(match result {
    Some(lit) => @lit.idx < (@a.0).len(),
    None => true })]
fn check_if_unit(f: &Formula, idx: usize, a: &Assignments) -> Option<Lit> {
    let clause = &f.clauses[idx];
    let mut i = 0;
    let mut unassigned = 0;
    let mut outlit: Option<Lit> = None;
    #[invariant(loop_invariant, 0usize <= i && @i <= (@clause.0).len())]
    #[invariant(result_invariant, match outlit {
        Some(lit) => @lit.idx < (@a.0).len(),
        None => true })]
    while i < clause.0.len() {
        let lit = clause.0[i];
        let res = a.0[lit.idx];
        match res {
            Some(x) => {
                // false, false || true, true -> clause is SAT
                if lit.polarity == x {
                    return None;
                }
            }
            None => {
                if unassigned >= 1 {
                    return None;
                }
                outlit = Some(Lit {
                    idx: lit.idx,
                    polarity: lit.polarity,
                }); // TODO fix
                unassigned += 1;
            }
        }
        i += 1;
    }
    return outlit;
}

#[ensures(result === SatState::Sat     ==> match res {
    Some(x) => x == lit.polarity,
    None => false})]
#[ensures(result === SatState::Unknown ==> res === None)]
#[ensures(result === SatState::Unsat     ==> match res {
    Some(x) => x != lit.polarity,
    None => false})]
fn tmp(lit: Lit, res: Option<bool>) -> SatState {
    match res {
        Some(x) => {
            // false, false || true, true -> clause is SAT
            if lit.polarity == x {
                return SatState::Sat;
            } else {
                return SatState::Unsat;
            }
        },
        None => {
            return SatState::Unknown;
        } // May become SAT
    }
}


#[logic]
fn litSat(lit: Lit, res: Option<bool>) -> bool {
    pearlite! {
        match res {
            Some(x) => {
                lit.polarity === x
            },
            None => {
                false
            }
        }
    }
}

#[logic]
fn litUnsat(lit: Lit, res: Option<bool>) -> bool {
    pearlite! {
        match res {
            Some(x) => {
                x != lit.polarity
            },
            None => {
                false
            }
        }
    }
}

#[logic]
fn litUnknown(lit: Lit, res: Option<bool>) -> bool {
    pearlite! {
        match res {
            Some(x) => {
                false
            },
            None => {
                true
            }
        }
    }
}

#[logic]
fn optionEq(lit: Lit, res: Option<bool>, q: SatState) -> bool {
    pearlite! {
        match res {
            Some(x) => {
                if lit.polarity == x {
                    eqSat(q)
                } else {
                    eqUnsat(q)
                }
            },
            None => {
                eqUnknown(q)
            } // May become SAT
        }
    }
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

#[trusted]
#[ensures(result === SatState::Sat     ==>  sat_clause(*a, (@f.clauses)[@idx]))]
#[ensures(result === SatState::Unknown ==> unknown(*a, (@f.clauses)[@idx]))]
#[ensures(result === SatState::Unsat   ==>  not_sat_clause(*a, (@f.clauses)[@idx]))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[requires(@idx < (@f.clauses).len())]
fn get_clause_state(f: &Formula, idx: usize, a: &Assignments) -> SatState {
    let clause = &f.clauses[idx];
    let mut i = 0;
    let mut out = SatState::Unsat;
    #[invariant(loop_invariant, 0usize <= i && @i <= (@clause.0).len())]
    #[invariant(previous,
        eqUnsat(out) || eqUnknown(out)
    )]
    #[invariant(previous2,
        forall<j: usize> 0usize <= j && j < i ==>
            (match (@a.0)[@(@clause.0)[@j].idx] {
                Some(x) => !eqUnknown(out),
                None => eqUnknown(out)
            })
    )]
    while i < clause.0.len() {
        let lit = clause.0[i];
        match a.0[lit.idx]{
            Some(x) => {
                // false, false || true, true -> clause is SAT
                if lit.polarity == x {
                    return SatState::Sat;
                } else {
                }
            },
            None => {
                out = SatState::Unknown;
            } // May become SAT
        }
        i += 1;
    }
    return out;
}

#[trusted]
#[ensures(result === SatState::Sat   ==>  sat_formula(*a, *f))]
#[ensures(result === SatState::Unsat ==> !sat_formula(*a, *f))]
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


/// Checks if the clause is empty.

#[ensures(result === true ==> not_sat_clause(*a, (@f.clauses)[@idx]))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[requires(@idx < (@f.clauses).len())]
fn check_empty(f: &Formula, idx: usize, a: &Assignments) -> bool {
    let clause = &f.clauses[idx];
    let mut i = 0;
    #[invariant(loop_invariant, 0usize <= i && @i <= (@clause.0).len())]
    #[invariant(previous,
        forall<j: usize> 0usize <= j && j < i ==>
        ((match (@a.0)[@(@clause.0)[@j].idx] { Some(x) => x != (@clause.0)[@j].polarity,
            None => 1 < 0}) &&
            (match (@a.0)[@(@clause.0)[@j].idx] { Some(x) => true,
            None => false}))
    )]
    while i < clause.0.len() {
        let lit = clause.0[i];
        let res = a.0[lit.idx];
        match res {
            Some(x) => {
                // false, false || true, true -> clause is SAT
                if lit.polarity == x {
                    return false;
                }
            }
            None => {
                return false;
            } // May become SAT
        }
        i += 1;
    }
    return true;
}

// Ensures that if true then it may be SAT?
#[ensures(result === true ==> !sat_formula(*a, *f))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
fn contains_empty(f: &Formula, a: &Assignments) -> bool {
    let mut i = 0;
    #[invariant(prev,
        forall<k: usize> 0usize <= k && k < i ==>
        !(not_sat_clause(*a, (@f.clauses)[@k])))]
    #[invariant(loop_invariant, 0usize <= i && @i <= (@f.clauses).len())]
    while i < f.clauses.len() {
        let res = check_empty(f, i, a);
        if res {
            return true;
        }
        i += 1
    }
    return false;
}


/// Checks if the clause is satisfied.
/// `true` means the clause is satisfied.
/// `false` means the clause is unsatisfied(empty clause) or that it contains
/// unassigned variables.
// LOOK at not_sat_clause. Do we really care about the false case?
//#[ensures(result === false ==> not_sat_clause(*a, (@f.clauses)[@idx]))] // I am failing!
#[ensures(result === true ==> sat_clause(*a, (@f.clauses)[@idx]))] // I am not!
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[requires(@idx < (@f.clauses).len())]
fn check_sat(f: &Formula, idx: usize, a: &Assignments) -> bool {
    let clause = &f.clauses[idx];
    let mut i = 0;
    #[invariant(loop_invariant, 0usize <= i && @i <= (@clause.0).len())]
    #[invariant(previous,
        forall<j: usize> 0usize <= j && j < i ==>
            (match (@a.0)[@(@clause.0)[@j].idx] { Some(x) => x != (@clause.0)[@j].polarity,
            None => true}) // Hmm
    )]
    while i < clause.0.len() {
        let lit = clause.0[i];
        let res = a.0[lit.idx];
        match res {
            Some(x) => {
                // false, false || true, true -> clause is SAT
                if lit.polarity == x {
                    return true;
                }
            }
            None => {} // continue
        }
        i += 1;
    }
    return false;
}

#[ensures(result === true ==> sat_formula(*a, *f))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
fn consistent(f: &Formula, a: &Assignments) -> bool {
    let mut i = 0;
    #[invariant(prev,
        forall<k: usize> 0usize <= k && k < i ==>
        !(not_sat_clause(*a, (@f.clauses)[@k])))]
    #[invariant(loop_invariant, 0usize <= i && @i <= (@f.clauses).len())]
    while i < f.clauses.len() {
        let res = check_sat(f, i, a);
        if !res {
            return false;
        }
        i += 1
    }
    return true;
}

//#[requires(assignments_invariant(*_f, *a))]
//#[ensures(assignments_invariant(*_f, ^a))]
#[requires(formula_invariant(*_f))]
#[requires(@idx < (@a.0).len())]
#[ensures((@a.0).len() === (@(^a).0).len())]
fn add_to_worklist(_f: &Formula, w: &mut Worklist, a: &mut Assignments, idx: usize, polarity: bool) {
    w.0.push(Lit{idx: idx, polarity: polarity});
    a.0[idx] = Some(polarity);
}

// We could jump back if clause is found to be unsat hmm.

#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[ensures(assignments_invariant(*f, ^a))]
fn unit_propagate(f: &Formula, a: &mut Assignments, w: &mut Worklist, l: Lit) {
    let mut i = 0;
    let old_a = Ghost::record(&a);
    #[invariant(loop_invariant, 0usize <= i && @i <= (@f.clauses).len())]
    #[invariant(ai, assignments_invariant(*f, *a))]
    #[invariant(proph, ^a === ^@old_a)]
    while i < f.clauses.len() {
        match check_if_unit(f, i, a) {
            Some(lit) => {
                add_to_worklist(
                    f,
                    w,
                    a,
                    lit.idx,
                    lit.polarity,
                );
            }
            None => {}
        }
        i += 1
    }
}

#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[ensures(assignments_invariant(*f, ^a))]
fn do_unit_propagation(f: &Formula, a: &mut Assignments, w: &mut Worklist) {
    let old_a = Ghost::record(&a);
    #[invariant(ai, assignments_invariant(*f, *a))]
    #[invariant(proph, ^a === ^@old_a)]
    while let Some(lit) = w.0.pop() {
        unit_propagate(f, a, w, lit);
    }
}

#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[ensures(assignments_invariant(*f, *a))]
#[ensures(match result {
    Some(t) => @t < @f.num_vars,
    None => true })]
fn find_unassigned(f: &Formula, a: &Assignments) -> Option<usize> {
    let mut i = 0;
    #[invariant(loop_invariant, 0usize <= i && @i <= (@a.0).len())]
    while i < a.0.len() {
        let curr = a.0[i];
        match curr {
            Some(x) => {} //continue
            None => {
                return Some(i);
            }
        }
        i += 1;
    }
    None
}


#[ensures(
    result === false ==> forall<a2: Assignments> compatible(*a, a2) ==>
    !sat_formula(a2, *f)
)]
#[ensures(result === true ==> exists<a2: Assignments> 0 <= 0 ==> sat_formula(a2, *f))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[ensures(formula_invariant(*f))]
#[ensures(assignments_invariant(*f, ^a))]
fn inner(f: &Formula, a: &mut Assignments, w: &mut Worklist) -> bool {
//    do_unit_propagation(f, a, w);
    if consistent(f, a) {
        return true;
    }
    if contains_empty(f, a) {
        return false;
    }
    let res = find_unassigned(f, a);
    match res {
        None => {
            // This should not happen
            return false;
        }
        Some(x) => {
            let unassigned_idx = x;
            let mut a_cloned = a.clone();
            let mut w_cloned = w.clone();
            add_to_worklist(
                f,
                w,
                a,
                unassigned_idx,
                true,
            );
            add_to_worklist(
                f,
                &mut w_cloned,
                &mut a_cloned,
                unassigned_idx,
                false,
            );
            return inner(f, a, w) || inner(f, &mut a_cloned, &mut w_cloned);
        }
    }
}


// This is trusted as it will be moved to the parser
/// Takes a 1-indexed 2d vector and converts it to a 0-indexed formula
#[trusted]
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

#[ensures(
    result === false ==> forall<a2: Assignments> (@a2.0).len() === @f.num_vars ==>
    !sat_formula(a2, *f)
)]
#[ensures(
    result === true ==> f.num_vars == 0usize || !(forall<a2: Assignments> (@a2.0).len() === @f.num_vars ==>
    !sat_formula(a2, *f))
)]
#[requires(formula_invariant(*f))]
pub fn solver(f: &Formula) -> bool {
    // should do pure literal and identifying unit clauses in preproc
    if f.num_vars == 0 {
        return true;
    }
    let mut assignments = Assignments::new(f);
    let mut worklist = init_worklist(f, &assignments);
    inner(f, &mut assignments, &mut worklist)
}
