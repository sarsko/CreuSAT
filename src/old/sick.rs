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
        };
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
        };
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
fn compatible_inner(a: Seq<AssignedState>, a2: Seq<AssignedState>) -> bool {
    pearlite! {
        a.len() === a2.len() &&
        forall<i: Int> 0 <= i && i < a.len() ==>
        (a[i] === AssignedState::Unset) || a[i] === a2[i]
    }
}

#[predicate]
fn compatible(a: Assignments, a2: Assignments) -> bool {
    pearlite! { compatible_inner(@(a.0), @(a2.0)) }
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
fn not_sat_clause_inner(a: Seq<AssignedState>, c: Clause) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < (@(c.0)).len() ==>
            match a[@(@c.0)[i].idx] {
                AssignedState::Positive => !(@(c.0))[i].polarity,
                AssignedState::Negative => (@(c.0))[i].polarity,
                AssignedState::Unset => false,
            }
    }
}

#[predicate]
fn not_sat_clause(a: Assignments, c: Clause) -> bool {
    pearlite! {
        not_sat_clause_inner(@(a.0), c)
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
        exists<a2 : Assignments> compatible(a, a2) && sat_formula(a2, f)
    }
}

#[predicate]
fn eventually_unsat_formula_inner(a: Seq<AssignedState>, f: Formula) -> bool {
    pearlite! {
        forall<a2: Seq<AssignedState>> compatible_inner(a, a2) ==> not_sat_formula_inner(a2, f)
    }
}

#[predicate]
fn eventually_unsat_formula(a: Assignments, f: Formula) -> bool {
    pearlite! { eventually_unsat_formula_inner(@(a.0), f) }
}

#[predicate]
fn not_sat_formula_inner(a: Seq<AssignedState>, f: Formula) -> bool {
    pearlite! {
        exists<i: Int> 0 <= i && i < (@(f.clauses)).len() &&
        not_sat_clause_inner(a, (@(f.clauses))[i])
    }
}

#[predicate]
fn not_sat_formula(a: Assignments, f: Formula) -> bool {
    pearlite! {
        exists<i: usize> 0usize <= i && @i < (@(f.clauses)).len() &&
        not_sat_clause(a, (@(f.clauses))[@i])
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
//#[requires((@(^a).0)[@idx] === AssignedState::Unset)]
#[requires(@idx < (@a.0).len())]
#[ensures((@a.0).len() === (@(^a).0).len())]
#[ensures(compatible(*a, ^a))]
#[ensures((@(^a).0)[@idx] === AssignedState::Positive || (@(^a).0)[@idx] === AssignedState::Negative)]
//#[ensures(unassigned_count(*a) > unassigned_count(^a))]
fn assign_ix(a: &mut Assignments, idx: usize, polarity: bool) {
    if polarity {
        a.0[idx] = AssignedState::Positive;
    } else {
        a.0[idx] = AssignedState::Negative;
    }
}

#[trusted]
#[ensures(result === eventually_unsat_formula(*a, *f))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
fn formula_is_unsat(f: &Formula, a: &Assignments) -> bool {
    panic!();
}

#[trusted]
#[ensures(result === sat_formula(*a, *f))]
#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
fn formula_is_sat(f: &Formula, a: &Assignments) -> bool {
    panic!();
}

#[trusted]
#[requires(unassigned_count(*a) > 0)]
#[ensures(@result < (@(a.0)).len())]
#[ensures((@(a.0))[@result] === AssignedState::Unset)]
fn find_unassigned(f: &Formula, a: &Assignments) -> usize {
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
                return i;
            }
            _ => {}
        }
        i += 1;
    }
    unreachable!()
}

#[logic]
#[requires(eventually_unsat_formula_inner(a.set(ix, AssignedState::Positive), f))]
#[requires(eventually_unsat_formula_inner(a.set(ix, AssignedState::Negative), f))]
#[ensures(eventually_unsat_formula_inner(a, f))]
fn lemma_omg(a: Seq<AssignedState>, ix: Int, f: Formula) {}

#[requires(formula_invariant(*f))]
#[requires(assignments_invariant(*f, *a))]
#[ensures(result === true ==> eventually_sat_formula(*a, *f))]
#[ensures(result === false ==> eventually_unsat_formula(*a, *f))]
fn inner(f: &Formula, a: &Assignments) -> bool {
    if formula_is_sat(f, a) {
        return true;
    }
    if formula_is_unsat(f, a) {
        return false;
    }
    let mut a_cloned = a.clone();
    let mut a_cloned2 = a.clone();

    let next = find_unassigned(f, a);

    a_cloned.0[next] = AssignedState::Positive;
    a_cloned2.0[next] = AssignedState::Negative;

    proof_assert! { { lemma_omg(@(a.0), 0, *f); true }}

    if inner(f, &a_cloned) {
        return true;
    } else {
        return inner(f, &a_cloned2);
    }
}
