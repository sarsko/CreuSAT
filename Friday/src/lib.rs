#![feature(type_ascription)]
#![cfg_attr(not(feature = "contracts"), feature(stmt_expr_attributes, proc_macro_hygiene))]
#![allow(unused_imports)]
#![allow(dead_code)]
#![recursion_limit = "256"]
extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;


// This is a very naive, but verified SAT solver.
// It is a port of a verified WhyML solver, and is therefore
// an imperative implementation of a functional prgram.
// In other words: very naive, very slow.

struct Assignment(Vec<bool>);
struct Lit {
    var: usize,
    value: bool,
}
struct Clause(Vec<Lit>);
struct Pasn {
    assign: Vec<bool>,
    ix: usize,
}
pub struct Formula {
    clauses: Vec<Clause>,
    num_vars: usize,
}

impl Clause {
    #[predicate]
    fn vars_in_range(self, n: Int) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self.0).len() ==>
                (@self.0)[i].vars_in_range(n)
        }
    }
}

impl Assignment {
    #[predicate]
    fn compatible(self, pa: Pasn) -> bool {
        pearlite! {
            (@pa.assign).len() === (@self.0).len() &&
                forall<i: Int> 0 <= i && i < @pa.ix ==>
                    (@pa.assign)[i] === (@self.0)[i]
        }
    }
}

impl Formula {
    #[predicate]
    fn invariant(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
                (@self.clauses)[i].vars_in_range(@self.num_vars)
        }
    }
    #[predicate]
    fn sat(self, a: Assignment) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
                (@self.clauses)[i].sat(a)
        }
    }
}

impl Lit {
    #[predicate]
    fn sat(self, a: Assignment) -> bool {
        pearlite! {
            (@a.0)[@self.var] == self.value
        }
    }
    #[predicate]
    fn vars_in_range(self, n: Int) -> bool {
        pearlite! {
            @self.var < n
        }
    }
}

impl Pasn {
    #[predicate]
    fn invariant(self, n: Int) -> bool {
        pearlite! {
            @self.ix <= (@self.assign).len() &&
                (@self.assign).len() === n
        }
    }
}

impl Clause {
    #[predicate]
    fn sat(self, a: Assignment) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@self.0).len() &&
                (@self.0)[i].sat(a)
        }
    }
}

impl Clone for Pasn {
    #[trusted]
    #[ensures(*self === result)]
    fn clone(&self) -> Self {
        Pasn {
            assign: self.assign.clone(),
            ix: self.ix,
        }
    }
}

#[requires(c.vars_in_range((@a.0).len()))]
#[ensures(result === c.sat(*a))]
fn interp_clause(a: &Assignment, c: &Clause) -> bool {
    let mut i: usize = 0;
    let clause_len = c.0.len();
    #[invariant(prev_not_sat, forall<j: Int> 0 <= j && j < @i ==> !(@c.0)[j].sat(*a))]
    #[invariant(loop_invariant, @i <= @clause_len)]
    while i < clause_len {
        let l = a.0[c.0[i].var];
        let r = c.0[i].value;
        if l == r {
            return true;
        }
        i += 1;
    }
    false
}

#[requires(f.invariant())]
#[requires((@a.0).len() === @f.num_vars)]
#[ensures(result === f.sat(*a))]
fn interp_formula(a: &Assignment, f: &Formula) -> bool {
    let mut i: usize = 0;
    #[invariant(prev_sat, forall<j: Int> 0 <= j && j < @i ==> (@f.clauses)[j].sat(*a))]
    #[invariant(loop_invariant, @i <= (@f.clauses).len())]
    while i < f.clauses.len() {
        if !interp_clause(a, &f.clauses[i]) {
            return false;
        }
        i += 1;
    }
    true
}

#[requires(@pa.ix < (@pa.assign).len())]
#[requires((@pa.assign).len() <= @usize::MAX)]
#[ensures(Assignment(result.assign).compatible(*pa))]
#[ensures((@result.assign)[@pa.ix] === b)]
#[ensures(@result.ix === @pa.ix + 1)]
fn set(pa: &Pasn, b: bool) -> Pasn {
    let mut new_pa = pa.clone();
    new_pa.assign[pa.ix] = b;
    new_pa.ix += 1;
    new_pa
}

#[variant(@f.num_vars - @pa.ix)]
#[requires(pa.invariant(@f.num_vars))]
#[requires(f.invariant())]
#[ensures(!result === forall<a: Assignment> a.compatible(pa) ==> !f.sat(a))]
fn inner(f: &Formula, pa: Pasn) -> bool {
    if pa.ix == pa.assign.len() {
        return interp_formula(&Assignment(pa.assign), f);
    } else {
        return inner(f, set(&pa, true)) || inner(f, set(&pa, false));
    }
}

#[ensures(!result ==> forall<a: Assignment> (@a.0).len() === @f.num_vars ==> !f.sat(a))]
#[ensures( result ==> exists<a: Assignment> f.sat(a))]
#[requires(f.invariant())]
pub fn solver(f: &Formula) -> bool {
    if f.clauses.len() == 0 {
        return true;
    }
    let mut assign: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    #[invariant(loop_invariant, @i <= @f.num_vars)]
    #[invariant(len_invariant, (@assign).len() === @i)]
    while i < f.num_vars {
        assign.push(false);
        i += 1
    }
    let base = Pasn {
        assign: assign,
        ix: 0,
    };
    inner(f, base)
}
