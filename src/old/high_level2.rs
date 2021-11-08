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
#[requires(-1 <= i)]
#[variant(i)]
#[ensures(result >= 0)]
#[ensures(@a.0 === @a.0)]
fn unassigned_count_internal(a: Assignments, i: Int) -> Int {
    pearlite! {
        if i === -1 {
            0
        } else {
            match (@a.0)[i] {
            AssignedState::Unset => 1 + unassigned_count_internal(a, i - 1),
            _ => unassigned_count_internal(a, i - 1)
            }
        }
    }
}

#[logic]
#[ensures(result >= 0)]
fn unassigned_count(a: Assignments) -> Int {
    pearlite! {
        unassigned_count_internal(a, (@a.0).len()-1)
    }
}


#[logic]
#[requires(-1 <= i)]
#[variant(i)]
#[ensures(result >= 0)]
#[ensures(result > 0 ==> exists<i: Int> a[i] === AssignedState::Unset)]
/*
#[ensures(result === 0 ==> forall<i: Int> 0 <= i && i < a.len() ==>
    match a[i] {
     AssignedState::Unset => false,
     _ => true,
})]
*/
//ensures(result === 0 ==> (forall<i: Int> 0 <= i && i < a.len() && !(a[i] === AssignedState::Unset)))]
fn unassigned_count_internal2(a: creusot_contracts::Seq<AssignedState>, i: Int) -> Int {
    pearlite! {
        if i === -1 {
            0
        } else {
            match a[i] {
            AssignedState::Unset => {1 + unassigned_count_internal2(a, i - 1)},
            _ => unassigned_count_internal2(a, i - 1)
            }
        }
    }
}
#[logic]
#[ensures(result >= 0)]
#[ensures(result > 0 ==> exists<i: Int> a[i] === AssignedState::Unset)]
#[ensures(result === 0 ==> !exists<i: Int> a[i] === AssignedState::Unset)]
fn unassigned_count2(a: creusot_contracts::Seq<AssignedState>) -> Int {
    pearlite! {
        unassigned_count_internal2(a, a.len()-1)
    }
}

#[ensures(result > 0usize === exists<i: usize> (@a.0)[@i] === AssignedState::Unset)]
//#[ensures(result === 0usize ==> !exists<i: usize> (@a.0)[@i] === AssignedState::Unset)]
#[ensures(result === 0usize ==> forall<i: usize> 0usize <= i && @i < (@a.0).len() ==>
    match (@a.0)[@i] {
     AssignedState::Unset => false,
     _ => true,
})]
#[ensures(@result === unassigned_count(*a))]
#[ensures(@result === unassigned_count2(@a.0))]
fn unassigned_count_rust(a: &Assignments) -> usize {
    let mut i = 0;
    let mut out = 0;
    #[invariant(bounds, out <= i)]
    #[invariant(sync, unassigned_count_internal(*a, @i-1) === @out)]
    #[invariant(loop_invariant, @i <= (@a.0).len())]
    #[invariant(not_zero, out > 0usize === exists<j: usize> j < i && (@a.0)[@j] === AssignedState::Unset)]
    #[invariant(zero, out === 0usize ==> !exists<j: usize> 0usize <= j && j < i && (@a.0)[@j] === AssignedState::Unset)]
    #[invariant(zero2, out === 0usize ==> forall<j: usize> 0usize <= j && j < i ==>
        match (@a.0)[@j] {
            AssignedState::Unset => false,
            _ => true,
    })]
    while i < a.0.len() {
        match a.0[i] {
            AssignedState::Unset => out += 1,
            _ => {},
        }
        i += 1;
    }
    out
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
        unassigned_count(a) === 0 &&
            (forall<i: usize> 0usize <= i && @i < (@(f.clauses)).len() ==>
        sat_clause(a, (@(f.clauses))[@i]))
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
    #[ensures(
        forall<i: usize> 0usize <= i && @i < (@result.0).len() ==>
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

#[requires((@(*a).0)[@idx] === AssignedState::Unset)]
#[requires(formula_invariant(*_f))]
#[requires(@idx < (@a.0).len())]
#[ensures((@(^a).0)[@idx] === AssignedState::Positive || (@(^a).0)[@idx] === AssignedState::Negative)]
#[ensures((@a.0).len() === (@(^a).0).len())]
#[ensures(compatible(*a, ^a))]
#[ensures(((@(*a).0)[@idx] === AssignedState::Unset) ==> (unassigned_count2(@a.0) === (unassigned_count2(@(^a).0) + 1)))]
//#[ensures(unassigned_count(*a) === (unassigned_count(^a) + 1))]
fn add_to_worklist(_f: &Formula, w: &mut Worklist, a: &mut Assignments, idx: usize, polarity: bool) {
    w.0.push(Lit{idx: idx, polarity: polarity});
    let old_a = Ghost::record(&a);
    let unset = AssignedState::Unset;
    if a.0[idx] != unset {
        return;
    }
    if polarity {
        assert!(unassigned_count_rust(a) > 0);
        a.0[idx] = AssignedState::Positive;
        proof_assert! {
            ((@(*@old_a).0)[@idx] === AssignedState::Unset) ==>
                (unassigned_count2(@(@old_a).0) === unassigned_count2(@(^(@old_a)).0) + 1) }
    } else {
        assert!(unassigned_count_rust(a) > 0);
        a.0[idx] = AssignedState::Negative;
        proof_assert! {
            ((@(*@old_a).0)[@idx] === AssignedState::Unset) ==>
                (unassigned_count2(@(@old_a).0) === unassigned_count2(@(^(@old_a)).0) + 1) }
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

#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[ensures(assignments_invariant(*f, *a))]
#[ensures(match result {
    Some(t) => @t < @f.num_vars,
    None => true
})]
#[ensures(match result {
    Some(i) => (@a.0)[@i] === AssignedState::Unset,
    None => true
})]
#[ensures(match result {
    Some(t) => unassigned_count(*a) > 0,
    None => unassigned_count(*a) === 0
})]
fn find_unassigned(f: &Formula, a: &Assignments) -> Option<usize> {
    let mut i = 0;
    #[invariant(loop_invariant, 0usize <= i && @i <= (@a.0).len())]
    #[invariant(prev, forall<j: usize> 0usize <= j && j < i ==>
        match (@a.0)[@j] {
            AssignedState::Unset => false,
            _ => true,
        })]
    /*
    #[invariant(unass, forall<j: usize> 0usize <= j && j < i ==>
        unassigned_count_internal(*a, @j) === 0
    )]
    */
    #[invariant(unass, unassigned_count_internal(*a, @i-1) === 0)]
    while i < a.0.len() {
        let curr = a.0[i];
        match curr {
            AssignedState::Unset => {
                assert!(unassigned_count_rust(a) > 0);
                proof_assert! {unassigned_count(*a) > 0 } // Dunno why this is failing
                return Some(i);
            },
            _ => {},
        }
        i += 1;
    }
    None
}

#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[ensures(assignments_invariant(*f, ^a))]
#[ensures(compatible(*a, ^a))]
#[ensures(result === (unassigned_count(*a) === unassigned_count(^a) + 1))]
#[ensures(!result === ((unassigned_count(*a) === unassigned_count(^a)) && (unassigned_count(^a) === 0)))]
#[ensures(!result === ((unassigned_count(*a) === 0)))]
#[ensures(!result === (unassigned_count(^a) === unassigned_count(*a)))]
#[ensures(!result ==> (unassigned_count(^a) === 0))]
#[ensures(!result === (
        (unassigned_count(*a) === unassigned_count(^a)) &&
        (unassigned_count(^a) === 0) &&
        (unassigned_count(*a) === 0)
        ))]
fn setnext(f: &Formula, a: &mut Assignments, w: &mut Worklist, p: bool) -> bool {
    let res = find_unassigned(f, a);
    match res {
        Some(x) => {
            add_to_worklist(
                f,
                w,
                a,
                x,
                p,
            );
            return true;
        },
        None => {
            proof_assert! {unassigned_count(^a) === 0}
            proof_assert! {unassigned_count(*a) === 0}
            return false;},
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
/*
#[ensures(
    result === false ==> forall<a2: Assignments> compatible_complete(*a, a2) ==>
    not_sat_formula(a2, *f)
)]
*/
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
*/
#[ensures(
    result === false ==> exists<a2: Assignments> compatible(*a, a2) &&
    !sat_formula(a2, *f)
)]
#[ensures(
    result === false ==> exists<a2: Assignments> compatible(*a, a2) &&
    not_sat_formula(a2, *f)
)]
// This is OK
#[ensures(result ==> exists<a2: Assignments> compatible(*a, a2) && sat_formula(a2, *f))]


#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[ensures(assignments_invariant(*f, ^a))]
//#[variant(unassigned_count(*a))]
#[requires(unassigned_count(*a) >= 0 )]
//#[ensures(unassigned_count(*a) === unassigned_count(^a) + 1)]
#[trusted]
fn inner(f: &Formula, a: &mut Assignments, w: &mut Worklist, p: bool) -> bool {
//    do_unit_propagation(f, a, w);
    let old_a = Ghost::record(&a);
    if !setnext(f, a, w, p) {
        proof_assert! {unassigned_count(^a) === 0 || unassigned_count(*a) === 0}
        panic!();
    }
    let old_a2 = Ghost::record(&a);
    proof_assert! {unassigned_count(*@old_a) === (unassigned_count(*a) + 1)}
    proof_assert! {unassigned_count(*a) === (unassigned_count(*@old_a2))}
    if formula_is_sat(f, a) {
        return true;
    }
    if formula_is_unsat(f, a) {
        return false;
    }
    let mut a_cloned = a.clone();
    let mut w_cloned = w.clone();
    let mut a_cloned2 = a.clone();
    let mut w_cloned2 = w.clone();
    if inner(f, &mut a_cloned2, &mut w_cloned2, true) {
        return true;
    } else {
        return inner(f, &mut a_cloned, &mut w_cloned, false);
    }
}

/*
#[ensures(
    result === Some(false) ==> forall<a2: Assignments> compatible_complete(*a, a2) ==>
    not_sat_formula(a2, *f)
)]
*/

#[ensures(
    result === Some(false) ==> !sat_formula(*a, *f)
)]
#[ensures(
    result === Some(false) ==> exists<a2: Assignments> compatible(*a, a2) &&
    !sat_formula(a2, *f)
)]
#[ensures(
    result === Some(false) ==> exists<a2: Assignments> compatible(*a, a2) &&
    not_sat_formula(a2, *f)
)]
// This is OK
#[ensures(result === Some(true) ==> exists<a2: Assignments> compatible(*a, a2) && sat_formula(a2, *f))]

#[requires(unassigned_count(*a) >= 0 )]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[ensures(assignments_invariant(*f, ^a))]
#[variant(unassigned_count(*a))]
fn inner2(f: &Formula, a: &mut Assignments, w: &mut Worklist, p: bool) -> Option<bool> {
    if formula_is_sat(f, a) {
        return Some(true);
    }
    if formula_is_unsat(f, a) {
        return Some(false);
    }
    if !setnext(f, a, w, p) {
        return None;
    }
    let mut a_cloned = a.clone();
    let mut w_cloned = w.clone();
    let mut a_cloned2 = a.clone();
    let mut w_cloned2 = w.clone();
    let res = inner2(f, &mut a_cloned, &mut w_cloned, true);
    match res {
        Some(true) => return Some(true),
        None => return None,
        Some(false) => {
            return inner2(f, &mut a_cloned2, &mut w_cloned2, false);
        }
    }
}

