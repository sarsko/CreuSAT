#![allow(non_snake_case)]
use creusot_std::{prelude::*, std::vec::vec};

// This is a very naive, but verified SAT solver.
// It is a port of a verified WhyML solver, and is therefore
// an imperative implementation of a functional prgram.
// In other words: very naive, very slow.

pub struct Assignments(Vec<bool>);
pub struct Lit {
    var: usize,
    value: bool,
}
pub struct Clause(Vec<Lit>);

pub struct Pasn {
    assign: Assignments,
    ix: usize,
}
pub struct Formula {
    clauses: Vec<Clause>,
    num_vars: usize,
}

impl View for Assignments {
    type ViewTy = Seq<bool>;
    #[logic]
    fn view(self) -> Self::ViewTy {
        pearlite! { self.0@ }
    }
}

impl Clone for Assignments {
    #[check(terminates)]
    #[ensures(result@ == self@)]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl View for Clause {
    type ViewTy = Seq<Lit>;

    #[logic]
    fn view(self) -> Self::ViewTy {
        pearlite! { self.0@ }
    }
}

impl Clone for Pasn {
    #[check(terminates)]
    #[ensures(self.eq_logic(result))]
    fn clone(&self) -> Self {
        Self { assign: self.assign.clone(), ix: self.ix }
    }
}

impl Invariant for Formula {
    #[logic(open(self))]
    fn invariant(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self.clauses@.len() ==>
                self.clauses@[i].vars_in_range(self.num_vars@)
        }
    }
}

impl Formula {
    #[logic(open(self))]
    pub fn num_vars(self) -> Int {
        pearlite! { self.num_vars@ }
    }

    #[logic(open(self))]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self.clauses@.len() ==>
                self.clauses@[i].sat(a)
        }
    }
}

impl Clause {
    #[logic(open(self))]
    fn vars_in_range(self, n: Int) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self@.len() ==>
                self@[i].var_in_range(n)
        }
    }
}

impl Lit {
    #[logic(open(self))]
    fn var_in_range(self, n: Int) -> bool {
        pearlite! {
            self.var@ < n
        }
    }

    #[logic(open(self))]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! {
            a@[self.var@] == self.value
        }
    }
}

impl Assignments {
    #[logic(open(self))]
    fn compatible(self, pa: Pasn) -> bool {
        pearlite! {
            pa.assign.0@.len() == self.0@.len() &&
                forall<i: Int> 0 <= i && i < pa.ix@ ==>
                    pa.assign@[i] == self@[i]
        }
    }
}

impl Pasn {
    #[logic(open(self))]
    pub fn eq_logic(self, rhs: Self) -> bool {
        pearlite! {
            self.assign@ == rhs.assign@ && self.ix == rhs.ix
        }
    }

    #[logic(open(self))]
    pub fn invariant(self, n: Int) -> bool {
        pearlite! {
            self.ix@ <= self.assign@.len()
            && self.assign@.len() == n
        }
    }
}

impl Clause {
    #[logic(open(self))]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < self@.len() &&
                self@[i].sat(a)
        }
    }
}

impl Clause {
    #[check(terminates)]
    #[requires(self.vars_in_range(a@.len()))]
    #[ensures(result == self.sat(*a))]
    fn eval(&self, a: &Assignments) -> bool {
        let mut i: usize = 0;
        let clause_len = self.0.len();
        #[variant(clause_len@ - i@)]
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
    #[check(terminates)]
    #[requires(a@.len() == self.num_vars@)]
    #[ensures(result == self.sat(*a))]
    fn eval(&self, a: &Assignments) -> bool {
        let mut i: usize = 0;
        #[variant(self.clauses@.len() - i@)]
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

#[check(terminates)]
#[requires(pa.ix@ < pa.assign@.len())]
#[requires(pa.assign@.len() <= usize::MAX@)]
#[ensures(result.assign.compatible(*pa))]
#[ensures(result.assign@[pa.ix@] == b)]
#[ensures(result.ix@ == pa.ix@ + 1)]
fn set_next(pa: &Pasn, b: bool) -> Pasn {
    let mut new_pa = pa.clone();
    new_pa.assign.0[pa.ix] = b;
    new_pa.ix += 1;
    new_pa
}

#[check(terminates)]
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
#[ensures(!result ==> forall<a: Assignments> a@.len() == f.num_vars()
                  ==> !f.sat(a))]
#[ensures( result ==> exists<a: Assignments> f.sat(a))]
pub fn solver(f: &Formula) -> bool {
    solve(f, Pasn { assign: Assignments(vec![false; f.num_vars]), ix: 0 })
}
