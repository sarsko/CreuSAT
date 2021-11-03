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

#[logic]
#[requires(0 <= i)]
#[variant(i)]
fn unassigned_count_internal(a: Assignments, i: Int) -> Int {
    pearlite! {
        if i === 0 {
            0
        } else {
            match (@a.0)[i] {
            AssignedState::Unset => {1 + unassigned_count_internal(a, i - 1)},
            _ => unassigned_count_internal(a, i - 1)
            }
        }
    }
}

#[logic]
fn unassigned_count(a: Assignments) -> Int {
    pearlite! {
        unassigned_count_internal(a, (@a.0).len()-1)
    }
}


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
fn compatible_complete(a: Assignments, a2: Assignments, f: Formula) -> bool {
    pearlite! {
        (@a2.0).len() === @f.num_vars &&
        forall<i: usize> 0usize <= i && @i < (@a.0).len() ==>
        ((((@a.0)[@i] === AssignedState::Unset &&
         !((@a.0)[@i] === AssignedState::Unset))) ||
         (@a.0)[@i] === (@a2.0)[@i])
    }
}

#[predicate]
fn compatible(a: Assignments, a2: Assignments) -> bool {
    pearlite! {
        (@a.0).len() === (@a2.0).len() &&
        forall<i: usize> 0usize <= i && @i < (@a.0).len() ==>
        (@a.0)[@i] === AssignedState::Unset || (@a.0)[@i] === (@a2.0)[@i]
    }
}

#[predicate]
fn complete(a: Assignments, f: Formula) -> bool {
    pearlite! {
        (@a.0).len() === @f.num_vars &&
        forall<i: usize> 0usize <= i && @i < (@a.0).len() ==>
        !((@a.0)[@i] === AssignedState::Unset)
    }
}

#[predicate]
fn not_sat_clause(a: Assignments, c: Clause) -> bool {
    pearlite! {
        forall<i: usize> 0usize <= i && @i < (@c.0).len() ==>
            match (@a.0)[@(@c.0)[@i].idx] {
                AssignedState::Positive => !(@c.0)[@i].polarity,
                AssignedState::Negative => (@c.0)[@i].polarity,
                AssignedState::Unset => false,
            }

    }
}

#[predicate]
fn sat_clause(a: Assignments, c: Clause) -> bool {
    pearlite! {
        exists<i: usize> 0usize <= i && @i < (@c.0).len() &&
            match (@a.0)[@(@c.0)[@i].idx] {
                AssignedState::Positive => (@c.0)[@i].polarity,
                AssignedState::Negative => !(@c.0)[@i].polarity,
                AssignedState::Unset => false,
            }
    }
}

#[predicate]
fn unknown(a: Assignments, c: Clause) -> bool {
    pearlite! {
        !sat_clause(a,c) && !not_sat_clause(a, c)
    }
}

#[predicate]
fn sat_formula(a: Assignments, f: Formula) -> bool {
    pearlite! {
        forall<i: usize> 0usize <= i && @i < (@(f.clauses)).len() ==>
        sat_clause(a, (@(f.clauses))[@i])
    }
}

#[predicate]
fn not_sat_formula(a: Assignments, f: Formula) -> bool {
    pearlite! {
        exists<i: usize> 0usize <= i && @i < (@(f.clauses)).len() &&
        not_sat_clause(a, (@(f.clauses))[@i])
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
        forall<i: usize> 0usize <= i && @i < (@self.0).len() ==>
        (@self.0)[@i] === (@result.0)[@i]
    )]
    #[ensures((@self.0).len() === (@result.0).len())]
    #[ensures(*self === result)]
    fn clone(&self) -> Self {
        Worklist(self.clone_lit_vector(&self.0))
    }
}

impl Assignments {
    #[trusted]
    fn clone_assignment_vector(&self, v: &Vec<AssignedState>) -> Vec<AssignedState> {
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
        forall<i: usize> 0usize <= i && @i < (@self.0).len() ==>
        (@self.0)[@i] === (@result.0)[@i]
    )]
    #[ensures((@self.0).len() === (@result.0).len())]
    #[ensures(*self === result)]
    fn clone(&self) -> Self {
        Assignments(self.clone_assignment_vector(&self.0))
    }

    #[requires(formula_invariant(*f))]
    #[ensures(assignments_invariant(*f, result))]
    fn new(f: &Formula) -> Self {
        let mut assign: Vec<AssignedState> = Vec::new();
        let mut i = 0;
        #[invariant(loop_invariant, 0usize <= i && i <= f.num_vars)]
        #[invariant(length_invariant, (@assign).len() === @i)]
        while i < f.num_vars {
            assign.push(AssignedState::Unset);
            i += 1
        }
        Assignments(assign)
    }
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
           AssignedState::Positive => {
                if lit.polarity {
                    return None
                }
            },
            AssignedState::Negative => {
                if !lit.polarity {
                    return None
                }
            },
            AssignedState::Unset => {
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


//#[requires(assignments_invariant(*_f, *a))]
//#[ensures(assignments_invariant(*_f, ^a))]
//#[requires((@a.0)[@idx] === AssignedState::Unset)] // TODO
//#[ensures(unassigned_count(^a) < unassigned_count(*a))]
#[ensures((@(^a).0)[@idx] === AssignedState::Positive || (@(^a).0)[@idx] === AssignedState::Negative)]
#[requires(formula_invariant(*_f))]
#[requires(@idx < (@a.0).len())]
#[ensures((@a.0).len() === (@(^a).0).len())]
#[ensures(compatible(*a, ^a))]
#[ensures(unassigned_count(*a) === unassigned_count(^a) + 1)]
fn add_to_worklist(_f: &Formula, w: &mut Worklist, a: &mut Assignments, idx: usize, polarity: bool) {
    w.0.push(Lit{idx: idx, polarity: polarity});
    if polarity {
        a.0[idx] = AssignedState::Positive;
    } else {
        a.0[idx] = AssignedState::Negative;
    }

}

// We could jump back if clause is found to be unsat hmm.
/*
#[ensures(
    forall<a2: Assignments> compatible(*a, a2) ==>
    sat_formula(a2, *f) ==> sat_formula(a, *f)
)]
#[ensures(
    sat_formula(a2, *f) ==> sat_formula(a, *f)
)]
*/
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
/*
#[ensures(match result {
    Some(t) => 0 < unassigned_count(*a),
    None => unassigned_count(*a) === 0})]
*/
fn find_unassigned(f: &Formula, a: &Assignments) -> Option<usize> {
    let mut i = 0;
    #[invariant(loop_invariant, 0usize <= i && @i <= (@a.0).len())]
    #[invariant(prev, forall<j: usize> 0usize <= j && j < i ==>
        match (@a.0)[@j] {
            AssignedState::Unset => false,
            _ => true,
        })]
    while i < a.0.len() {
        let curr = a.0[i];
        match curr {
            AssignedState::Unset => {
                return Some(i);
            },
            _ => {},
        }
        i += 1;
    }
    None
}

#[ensures(result  === not_sat_clause(*a, (@f.clauses)[@idx]))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[requires(@idx < (@f.clauses).len())]
fn is_clause_unsat(f: &Formula, idx: usize, a: &Assignments) -> bool {
    let clause = &f.clauses[idx];
    let mut i = 0;
    #[invariant(loop_invariant, 0usize <= i && @i <= (@clause.0).len())]
    #[invariant(previous, forall<j: usize> 0usize <= j && j < i ==>
        match (@a.0)[@(@clause.0)[@j].idx] {
            AssignedState::Positive => !(@clause.0)[@j].polarity,
            AssignedState::Negative => (@clause.0)[@j].polarity,
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

#[ensures(result === true ==> not_sat_formula(*a, *f))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
fn formula_is_unsat(f: &Formula, a: &Assignments) -> bool {
    let mut i = 0;
    #[invariant(prev,
        forall<k: usize> 0usize <= k && k < i ==>
        !not_sat_clause(*a, (@f.clauses)[@k]))]
    #[invariant(loop_invariant, 0usize <= i && @i <= (@f.clauses).len())]
    while i < f.clauses.len() {
        if is_clause_unsat(f, i, a) {
            return true;
        }
        i += 1;
    }
    return false;
}

#[ensures(result ==>  sat_clause(*a, (@f.clauses)[@idx]))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[requires(@idx < (@f.clauses).len())]
fn is_clause_sat(f: &Formula, idx: usize, a: &Assignments) -> bool {
    let clause = &f.clauses[idx];
    let mut i = 0;
    #[invariant(previous, forall<j: usize> 0usize <= j && j < i ==>
        match (@a.0)[@(@clause.0)[@j].idx] {
            AssignedState::Positive => !(@clause.0)[@j].polarity,
            AssignedState::Negative => (@clause.0)[@j].polarity,
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


#[ensures(result === true  ==>  sat_formula(*a, *f))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
fn formula_is_sat(f: &Formula, a: &Assignments) -> bool {
    let mut i = 0;
    #[invariant(prev,
        forall<k: usize> 0usize <= k && k < i ==>
        sat_clause(*a, (@f.clauses)[@k]))]
    #[invariant(loop_invariant, 0usize <= i && @i <= (@f.clauses).len())]
    while i < f.clauses.len() {
        if !is_clause_sat(f, i, a) {
            return false;
        }
        i += 1
    }
    return true;
}

/*
#[ensures(
    result === false ==> forall<a2: Assignments> compatible(*a, a2) ==>
    !sat_formula(a2, *f)
)]
*/
#[ensures(
    result === false ==> forall<a2: Assignments> compatible_complete(*a, a2, *f) ==>
    not_sat_formula(a2, *f)
)]
/*
#[ensures(
    result === true ==> exists<a2: Assignments> compatible(*a, a2) && sat_formula(a2, *f)
)]
*/
#[ensures(result === true ==> exists<a2: Assignments> sat_formula(a2, *f))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[ensures(assignments_invariant(*f, ^a))]
//#[variant(unassigned_count(*a))]
fn inner(f: &Formula, a: &mut Assignments, w: &mut Worklist) -> bool {
//    do_unit_propagation(f, a, w);
    if formula_is_sat(f, a) {
        return true;
    }
    if formula_is_unsat(f, a) {
        return false;
    }
    let res = find_unassigned(f, a);
    match res {
        None => {
            // This should not happen
            panic!(); // TODO: Fix/prove unreachable
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
            if inner(f, a, w) {
                return true;
            } else {
                add_to_worklist(
                    f,
                    &mut w_cloned,
                    &mut a_cloned,
                    unassigned_idx,
                    false,
                );
             return inner(f, &mut a_cloned, &mut w_cloned);
            }
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

//#[trusted]
#[ensures(
    result === false ==> forall<a2: Assignments> complete(a2, *f)  ==>
    not_sat_formula(a2, *f)
)]
#[ensures(
    result === true ==> f.num_vars == 0usize || exists<a2: Assignments> sat_formula(a2, *f)
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
