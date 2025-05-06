#![allow(non_snake_case)]
//#![feature(type_ascription)]

use creusot_contracts::{std::clone::Clone, std::*, vec, *};

// This is a very naive, but verified SAT solver.
// It is a port of a verified WhyML solver, and is therefore
// an imperative implementation of a functional prgram.
// In other words: very naive, very slow.

#[derive(Clone)]
struct Assignments(Vec<bool>);
struct Lit {
    var: usize,
    value: bool,
}
struct Clause(Vec<Lit>);

#[derive(Clone)]
struct Pasn {
    assign: Assignments,
    ix: usize,
}
pub struct Formula {
    clauses: Vec<Clause>,
    num_vars: usize,
}

impl Invariant for Formula {
    #[predicate]
    #[open(self)]
    fn invariant(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self.clauses@.len() ==>
                self.clauses@[i].vars_in_range(self.num_vars@)
        }
    }
}

impl Formula {
    #[predicate]
    #[open(self)]
    fn sat(self, a: Assignments) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self.clauses@.len() ==>
                self.clauses@[i].sat(a)
        }
    }
}

impl Clause {
    #[predicate]
    #[open(self)]
    fn vars_in_range(self, n: Int) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self.0@.len() ==>
                self.0@[i].var_in_range(n)
        }
    }
}

impl Lit {
    #[predicate]
    #[open(self)]
    fn var_in_range(self, n: Int) -> bool {
        pearlite! {
            self.var@ < n
        }
    }

    #[predicate]
    #[open(self)]
    fn sat(self, a: Assignments) -> bool {
        pearlite! {
            a.0@[self.var@] == self.value
        }
    }
}

impl Assignments {
    #[predicate]
    #[open(self)]
    fn compatible(self, pa: Pasn) -> bool {
        pearlite! {
            pa.assign.0@.len() == self.0@.len() &&
                forall<i: Int> 0 <= i && i < pa.ix@ ==>
                    pa.assign.0@[i] == self.0@[i]
        }
    }
}

impl Pasn {
    #[predicate]
    #[open(self)]
    fn invariant(self, n: Int) -> bool {
        pearlite! {
            self.ix@ <= self.assign.0@.len()
            && self.assign.0@.len() == n
        }
    }
}

impl Clause {
    #[predicate]
    #[open(self)]
    fn sat(self, a: Assignments) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < self.0@.len() &&
                self.0@[i].sat(a)
        }
    }
}

impl Clause {
    #[requires(self.vars_in_range(a.0@.len()))]
    #[ensures(result == self.sat(*a))]
    fn eval(&self, a: &Assignments) -> bool {
        let mut i: usize = 0;
        let clause_len = self.0.len();
        #[invariant(forall<j: Int> 0 <= j && j < i@ ==> !self.0@[j].sat(*a))]
        #[invariant(i@ <= clause_len@)]
        while i < clause_len {
            if a.0[self.0[i].var] == self.0[i].value {
                return true;
            }
            i += 1;
        }
        false
    }
}

impl Formula {
    #[requires(a.0@.len() == self.num_vars@)]
    #[ensures(result == self.sat(*a))]
    fn eval(&self, a: &Assignments) -> bool {
        let mut i: usize = 0;
        #[invariant(forall<j: Int> 0 <= j && j < i@ ==> self.clauses@[j].sat(*a))]
        while i < self.clauses.len() {
            if !self.clauses[i].eval(a) {
                return false;
            }
            i += 1;
        }
        true
    }
}

#[requires(pa.ix@ < pa.assign.0@.len())]
#[requires(pa.assign.0@.len() <= usize::MAX@)]
#[ensures(result.assign.compatible(*pa))]
#[ensures(result.assign.0@[pa.ix@] == b)]
#[ensures(result.ix@ == pa.ix@ + 1)]
fn set_next(pa: &Pasn, b: bool) -> Pasn {
    let mut new_pa = pa.clone();
    new_pa.assign.0[pa.ix] = b;
    new_pa.ix += 1;
    new_pa
}

#[variant(f.num_vars@ - pa.ix@)]
#[requires(pa.invariant(f.num_vars@))]
#[requires(f.invariant())]
#[ensures(!result == (forall<a: Assignments> a.compatible(pa) ==> !f.sat(a)))]
fn solve(f: &Formula, pa: Pasn) -> bool {
    if pa.ix == pa.assign.0.len() {
        return f.eval(&pa.assign);
    }
    solve(f, set_next(&pa, true)) || solve(f, set_next(&pa, false))
}

#[requires(f.invariant())]
#[ensures(!result ==> forall<a: Assignments> a.0@.len() == f.num_vars@
                  ==> !f.sat(a))]
#[ensures( result ==> exists<a: Assignments> f.sat(a))]
pub fn solver(f: &Formula) -> bool {
    solve(f, Pasn { assign: Assignments(vec![false; f.num_vars]), ix: 0 })
}
