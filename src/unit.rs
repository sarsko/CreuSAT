#![feature(type_ascription)]

extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

//ghost.rs
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

fn main() {}

// clause.rs
pub struct Clause(pub Vec<Lit>);

impl Model for Clause {
    type ModelTy = Seq<Lit>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        self.0.model()
    }
}

#[predicate]
pub fn vars_in_range_internal(c: Seq<Lit>, n: Int) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < c.len() ==>
            (0 <= @(c[i]).idx && @(c[i]).idx < n)
    }
}

impl Clause {
    #[predicate]
    pub fn vars_in_range(self, n: Int) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self).len() ==>
                (0 <= @((@self)[i]).idx && @((@self)[i]).idx < n)
        }
    }
}

// Okay screw unass, true and false is where it is at

#[logic]
#[variant(c.len())]
pub fn false_count(a: Seq<Option<bool>>, c: Seq<Lit>) -> Int {
    if pearlite! { c.len() === 0 }{
        0
    } else if pearlite! { a[@c[0].idx] === Some(c[0].polarity) ||
    a[@c[0].idx] === None } {
        1 + false_count(a, c.tail())
    } else {
        false_count(a, c.tail())
    }
}

#[logic]
#[variant(c.len())]
#[requires(vars_in_range_internal(c, a.len()))]
#[ensures(0 <= result && result <= c.len())]
pub fn true_count(a: Seq<Option<bool>>, c: Seq<Lit>) -> Int {
    if pearlite! { c.len() === 0 }{
        0
    } else if pearlite! { a[@c[0].idx] === Some(c[0].polarity) } {
        1 + true_count(a, c.tail())
    } else {
        true_count(a, c.tail())
    }
}

#[logic]
#[variant(c.len())]
#[requires(vars_in_range_internal(c, a.len()))]
#[ensures(0 <= result && result <= c.len())]
#[ensures(result === true_count(a, c))]
fn true_count2(a: Seq<Option<bool>>, c: Seq<Lit>) -> Int {
    if pearlite! { c.len() === 0 }{
        0
    } else {
        pearlite! { match (a[@c[0].idx], c[0].polarity) {
        (Some(true), true) => 1 + true_count2(a, c.tail()),
        (Some(false), false) => 1 + true_count2(a, c.tail()),
        _ => true_count2(a, c.tail())
        }
    }
    }
}

#[logic]
#[variant(c.len() - i)]
#[requires(0 <= i && i <= c.len())]
#[requires(vars_in_range_internal(c, a.len()))]
#[ensures(0 <= result )]
#[ensures(result <= c.len())]
//#[ensures(result <= i)]
//#[ensures(result === true_count(a, c))]
fn true_count_with_idx(a: Seq<Option<bool>>, c: Seq<Lit>, i: Int) -> Int {
    if pearlite! { i === c.len() }{
        0
    } else {
         match pearlite! {(a[@c[i].idx], c[i].polarity)} {
            (Some(true), true) => 1 + true_count_with_idx(a, c, i + 1),
            (Some(false), false) => 1 + true_count_with_idx(a, c, i + 1),
            _ => true_count_with_idx(a, c, i + 1)
        }

    }
}

#[logic]
#[variant(c.len() - from)]
#[requires(0 <= from && from <= c.len())]
#[requires(0 <= end && end <= c.len())]
#[requires(from <= end)]
#[requires(vars_in_range_internal(c, a.len()))]
#[ensures(0 <= result)]
#[ensures(result <= c.len())]
//#[ensures(result <= i)]
//#[ensures(result === true_count(a, c))]
fn true_count_range(a: Seq<Option<bool>>, c: Seq<Lit>, from: Int, end: Int) -> Int {
    if pearlite! { from === end }{
        0
    } else {
         match pearlite! {(a[@c[from].idx], c[from].polarity)} {
            (Some(true), true) => 1 + true_count_range(a, c, from + 1, end),
            (Some(false), false) => 1 + true_count_range(a, c, from + 1, end),
            _ => true_count_range(a, c, from + 1, end)
        }

    }
}


#[logic]
#[variant(c.len() - from)]
#[requires(0 <= from && from <= c.len())]
#[requires(0 <= end && end <= c.len())]
#[requires(from <= end)]
#[requires(vars_in_range_internal(c, a.len()))]
#[ensures(0 <= result)]
//#[ensures(result <= c.len())]
//#[ensures(result <= end)]
fn length(a: Seq<Option<bool>>, c: Seq<Lit>, from: Int, end: Int) -> Int {
    if pearlite! { from >= end }{
        0
    } else {
        1 + length(a, c, from + 1, end)
    }
}

#[logic]
#[ensures(result === length(a, c, 0, c.len()))]
fn length_log(a: Seq<Option<bool>>, c: Seq<Lit>) -> Int {
    pearlite! { c.len() }
}

#[logic]
fn filter_true(a: Seq<Option<bool>>, c: Seq<Lit>) -> Seq<Lit> {
    if pearlite! { c.len() === 0 }{
        panic!()
    } else {
        pearlite! {
            match (a[@c[0].idx], c[0].polarity) {
                    (Some(true), true) => Seq::cons(c[0], filter_true(a, c.tail())),
                    (Some(false), false) => Seq::cons(c[0], filter_true(a, c.tail())),
                    _ => filter_true(a, c.tail())
            }
        }
    }
}

//#[ensures(@result === length(@a, @c, 0, (@c).len()))]
#[ensures(@result === length_log(@a, @c))]
fn length_rs(a: &Assignments, c: &Clause) -> usize {
    return c.0.len()
}

#[requires(c.vars_in_range((@a).len()))]
//#[ensures(@result === true_count(@a, @c))]
//#[ensures(@result === true_count2(@a, @c))]
#[ensures(@result === true_count_range(@a, @c, 0, (@c).len()))]
fn count_trues(a: &Assignments, c: &Clause) -> usize {
    let mut out: usize = 0;
    let mut i: usize = 0;
    #[invariant(loop_invariant, 0 <= @i && @i <= (@c).len())]
    #[invariant(still_in, c.vars_in_range((@a).len()))]
    #[invariant(out_less, @out <= @i)]
    #[invariant(in_sync, @out === true_count_range(@a, @c, 0, @i))]
    while i < c.0.len() {
        let res = a.0[c.0[i].idx];
        match res {
            Some(b) => {
                if b == c.0[i].polarity {
                    out += 1;
                }
            }
            None => {}
        }
        i += 1;
    }
    out
}


#[logic]
#[variant(c.len())]
pub fn unassigned_count_clause_partial(c: Seq<Lit>, a: Seq<Option<bool>>, i: Int) -> Int {
    if c.len() == 0 || i == 0 {
        0
    } else if pearlite! { a[@c[0].idx] === None } {
        1 + unassigned_count_clause_partial(c.tail(), a, i - 1)
    } else {
        unassigned_count_clause_partial(c.tail(), a, i - 1)
    }
}

#[logic]
#[variant(c.len())]
pub fn unassigned_count_clause(a: Seq<Option<bool>>, c: Seq<Lit>) -> Int {
    if pearlite! { c.len() === 0 }{
        0
    } else if pearlite! { a[@c[0].idx] === None } {
        1 + unassigned_count_clause(a, c.tail())
    } else {
        unassigned_count_clause(a, c.tail())
    }
}

#[predicate]
pub fn sat_clause_inner(a: Seq<Option<bool>>, c: Seq<Lit>) -> bool {
    pearlite! {
        exists<i: Int> 0 <= i && i < (c).len() &&
            match a[@(c)[i].idx] {
                Some(b) => (c)[i].polarity === b,
                None => false,
            }
    }
}

#[predicate]
fn clause_unit2(a: Seq<Option<bool>>, c: Seq<Lit>) -> bool {
    pearlite! {
        unassigned_count_clause(a, c) === 1 && !sat_clause_inner(a, c)
    }
}

#[predicate]
fn clause_unit(a: Seq<Option<bool>>, c: Seq<Lit>) -> bool {
    pearlite! {
        false_count(a, c) + 1 === c.len() && true_count(a, c) === 0
    }
}

impl Clause {
    #[predicate]
    pub fn unit(self, a: Assignments) -> bool {
        pearlite!{ clause_unit(@a, @self) }
    }

    #[predicate]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@self).len() &&
                match (@a)[@(@self)[i].idx] {
                    Some(b) => (@self)[i].polarity == b,
                    None => false,
                }
        }
    }
}

// lit.rs
#[derive(Clone, Copy)]
pub struct Lit {
    pub idx: usize,
    pub polarity: bool,
}

// Predicates
impl Lit {
    #[predicate]
    pub fn lit_in(self, c: Clause) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@c).len() &&
                (@c)[i] === self
        }
    }
}

// assignments.rs
pub struct Assignments(pub Vec<Option<bool>>);

impl Model for Assignments {
    type ModelTy = Seq<Option<bool>>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        self.0.model()
    }
}

#[predicate]
pub fn assignments_equality(a: Assignments, a2: Assignments) -> bool {
    pearlite! {
        (@a).len() === (@a2).len() &&
        forall<i: Int> 0 <= i && i < (@a).len() ==> (@a)[i] === (@a2)[i]
    }
}

#[predicate]
pub fn compatible_inner(a: Seq<Option<bool>>, a2: Seq<Option<bool>>) -> bool {
    pearlite! {
        a.len() === a2.len() &&
        forall<i: Int> 0 <= i && i < a.len() ==>
        (a[i] === None) || a[i] === a2[i]
    }
}

#[predicate]
pub fn complete_inner(a: Seq<Option<bool>>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < a.len() ==> !(a[i] === None)
    }
}

#[predicate]
pub fn compatible_complete_inner(a: Seq<Option<bool>>, a2: Seq<Option<bool>>) -> bool {
    pearlite! {
        compatible_inner(a, a2) && complete_inner(a2)
    }
}


// formula.rs
pub struct Formula {
    pub clauses: Vec<Clause>,
    pub num_vars: usize,
}


// This is the shit that should be solved

fn unit_prop(f: &Formula, a: &mut Assignments) -> bool {
    return false;
}

/*
#[logic]
#[requires(clause_unit(a, c))]
#[ensures(clause_unit2(a, c))]
fn lemma_unit_defs_are_equal(a: Seq<Option<bool>>, c: Seq<Lit>) {
}
*/

#[logic]
#[requires(clause_unit(a, c))]
#[requires(a[i] === None)]
#[ensures(clause_unit(a, c))]
fn lemma_unit_imples(a: Seq<Option<bool>>, c: Seq<Lit>, i: Int) {
}

#[logic]
//#[requires(false_count(a, c) + 1 === c.len())]
#[requires(true_count(a, c) === 0)]
#[requires(0 <= i && i < a.len())]
#[requires(a[i] === None)]
#[requires(@c[j].idx === i)]
#[ensures(
    true_count(a.set(i, Some(true)), c) === true_count(a, c) + 1
)]
#[ensures(a.set(i, Some(false))[i] === Some(false))]
fn false_assign_decreases(a: Seq<Option<bool>>, c: Seq<Lit>, i: Int, j: Int) {
}



