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
    #[trusted]
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
    #[trusted]
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
fn assignments_equality(a: Assignments, a2: Assignments) -> bool {
    pearlite! {
        (@a.0).len() === (@a2.0).len() &&
        forall<i: usize> 0usize <= i && @i < (@a.0).len() ==>
        (@a.0)[@i] === (@a2.0)[@i]
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
fn compatible(a: Assignments, a2: Assignments) -> bool {
    pearlite! {
        (@a.0).len() === (@a2.0).len() &&
        forall<i: usize> 0usize <= i && @i < (@a.0).len() ==>
        (@a.0)[@i] === AssignedState::Unset || (@a.0)[@i] === (@a2.0)[@i]
    }
}

#[predicate]
fn compatible_complete(a: Assignments, a2: Assignments) -> bool {
    pearlite! {
        (@a.0).len() === (@a2.0).len() &&
        forall<i: usize> 0usize <= i && @i < (@a.0).len() ==>
        ((@a.0)[@i] === AssignedState::Unset &&
        ( (@a2.0)[@i] === AssignedState::Negative || (@a2.0)[@i] === AssignedState::Positive ))
        || (@a.0)[@i] === (@a2.0)[@i]
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
                AssignedState::Unset => !(@c.0)[@i].polarity && (@c.0)[@i].polarity
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
fn eventually_sat_formula(a: Assignments, f: Formula) -> bool {
    pearlite! {
        exists<a2: Assignments> compatible_complete(a, a2) &&
            sat_formula(a2, f)
    }
}

#[predicate]
fn eventually_unsat_formula(a: Assignments, f: Formula) -> bool {
    pearlite! {
        forall<a2: Assignments> compatible_complete(a, a2) ==>
            not_sat_formula(a2, f)

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

    #[trusted]
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

#[trusted]
#[requires((@(*a).0)[@idx] === AssignedState::Unset)]
#[ensures(polarity ==> (@(^a).0)[@idx] === AssignedState::Positive )]
#[ensures(!polarity ==> (@(^a).0)[@idx] === AssignedState::Negative)]
#[requires(formula_invariant(*_f))]
#[requires(@idx < (@a.0).len())]
#[ensures((@a.0).len() === (@(^a).0).len())]
#[ensures(compatible(*a, ^a))]
//#[ensures(unassigned_count(*a) > unassigned_count(^a))]
fn add_to_worklist(_f: &Formula, w: &mut Worklist, a: &mut Assignments, idx: usize, polarity: bool) {
    w.0.push(Lit{idx: idx, polarity: polarity});
    if polarity {
        a.0[idx] = AssignedState::Positive;
    } else {
        a.0[idx] = AssignedState::Negative;
    }

}

#[trusted]
#[ensures(result === not_sat_formula(*a, *f))]
#[ensures(result ==> !sat_formula(*a, *f))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
fn formula_is_unsat(f: &Formula, a: &Assignments) -> bool {
    panic!();
}

#[trusted]
#[ensures(result === sat_formula(*a, *f))]
#[ensures(result ==> !not_sat_formula(*a, *f))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
fn formula_is_sat(f: &Formula, a: &Assignments) -> bool {
    panic!();
}

#[trusted]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[ensures(assignments_invariant(*f, *a))]
#[ensures(match result {
    Some(t) => @t < @f.num_vars,
    None => true })]
#[ensures(match result {
    Some(t) => 0 < unassigned_count(*a),
    None => unassigned_count(*a) === 0})]
#[ensures(match result {
    Some(t) => (@a.0)[@t] === AssignedState::Unset,
    None => true})]
//#[requires(unassigned_count(*a) > 0)]
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



#[ensures(0<=0)]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[ensures(assignments_invariant(*f, ^a))]
#[ensures(compatible(*a, ^a))]
//#[requires(unassigned_count(*a) > 0)]
//#[ensures(unassigned_count(^a) < unassigned_count(*a))] //|| unassigned_count(*a) === 0)]
fn setnext(f: &Formula, a: &mut Assignments, w: &mut Worklist, p: bool) {
    let res = find_unassigned(f, a);
    match res {
        Some(x) => {
            proof_assert! { (@(*a).0)[@x] === AssignedState::Unset}
            add_to_worklist(
                f,
                w,
                a,
                x,
                p,
            );
        },
        None => {},
    }
}

/*
// ONE GOAL CHECKS OUT AFTER SWAPPING TO usize
#[ensures(
    result === false ==> !exists<a2: Assignments> compatible_complete(*a, a2) &&
    sat_formula(a2, *f)
)]
*/
// ONE GOAL CHECKS OUT AFTER SWAPPING TO usize
#[ensures(
    result === false ==> forall<a2: Assignments> compatible_complete(*a, a2) ==>
    not_sat_formula(a2, *f)
)]
// ONE GOAL CHECKS OUT AFTER SWAPPING TO usize
 /*
#[ensures(
    result === false ==> forall<a2: Assignments> compatible(*a, a2) ==>
    not_sat_formula(a2, *f)
)]
 */

// Proving(but not what I want to prove:
/*
#[ensures(
    result === false ==> !sat_formula(*a, *f)
)]
#[ensures(
    result === false ==> exists<a2: Assignments> compatible(*a, a2) &&
    !sat_formula(a2, *f)
)]
#[ensures(
    result === false ==> exists<a2: Assignments> compatible(*a, a2) &&
    not_sat_formula(a2, *f)
)]

#[ensures(
    result === false ==> exists<a2: Assignments> compatible_complete(*a, a2) &&
    !sat_formula(a2, *f)
)]
#[ensures(
    result === false ==> exists<a2: Assignments> compatible_complete(*a, a2) &&
    not_sat_formula(a2, *f)
)]
*/
// This is OK
#[ensures(result ==> exists<a2: Assignments> compatible(*a, a2) && sat_formula(a2, *f))]
//#[ensures(result === exists<a2: Assignments> compatible(*a, a2) && sat_formula(a2, *f))]

#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
//#[ensures(assignments_invariant(*f, ^a))]
//#[variant(unassigned_count(*a))]
fn inner(f: &Formula, a: &Assignments, w: &Worklist) -> bool {
//    do_unit_propagation(f, a, w);
    let old_a = Ghost::record(&a);
    if formula_is_sat(f, a) {
  //      proof_assert! { sat_formula(*a, *f) }
        return true;
    }
  //  proof_assert! { !sat_formula(*a, *f) }
    if formula_is_unsat(f, a) {
 //       proof_assert! { not_sat_formula(*a, *f) }
        return false;
    }
//    proof_assert! { unassigned_count(*a) > 0 }
//    proof_assert! { !not_sat_formula(*a, *f) }
    let mut a_cloned = a.clone();
    let mut w_cloned = w.clone();
    let mut a_cloned2 = a.clone();
    let mut w_cloned2 = w.clone();
    let old_a = Ghost::record(&a_cloned);
//    proof_assert! {assignments_equality(*a, a_cloned)}
//    proof_assert! {assignments_equality(*a, a_cloned2)}
    setnext(f, &mut a_cloned, &mut w_cloned, true);
//    proof_assert! {unassigned_count(a_cloned) ===  unassigned_count(*a) + 1}
//    proof_assert! {compatible(*a, a_cloned)}
    if inner(f, &a_cloned, &w_cloned) {
        return true;
    } else {
        setnext(f, &mut a_cloned2, &mut w_cloned2, false);
        if inner(f, &a_cloned2, &w_cloned2) {
            return true;
        } else {
            return false;
        }

    }
}