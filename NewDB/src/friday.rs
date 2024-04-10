extern crate creusot_contracts;

use creusot_contracts::{std::clone::Clone, std::*, vec, *};

use crate::{assignments::*, lit::*};

struct Clause(Vec<Lit>);

#[derive(Clone)]
struct Pasn {
    assign: Assignments,
    ix: usize,
}

impl Assignments {
    #[open]
#[predicate]
    fn compatible(self, pa: Pasn) -> bool {
        pearlite! {
            self.invariant() &&
            pa.assign.0@.len() == self.0@.len() &&
                forall<i: Int> 0 <= i && i < pa.ix@ ==>
                    pa.assign.0@[i] == self.0@[i]
        }
    }
}
pub struct Formula {
    clauses: Vec<Clause>,
    num_vars: usize,
}

impl Formula {
    #[open]
#[predicate]
    fn invariant(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self.clauses@.len() ==>
                self.clauses@[i].vars_in_range(self.num_vars@)
        }
    }

    #[open]
#[predicate]
    fn sat(self, a: Assignments) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self.clauses@.len() ==>
                self.clauses@[i].clause_sat_logic(a)
        }
    }
}

impl Clause {
    #[open]
#[predicate]
    fn vars_in_range(self, n: Int) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self.0@.len() ==>
                self.0@[i].var_in_range(n)
        }
    }
}

impl Pasn {
    #[open]
#[predicate]
    fn invariant(self, n: Int) -> bool {
        pearlite! {
            self.ix@ <= self.assign.0@.len()
            && self.assign.0@.len() == n
            && self.assign.invariant()
        }
    }
}

impl Clause {
    #[open]
#[predicate]
    fn clause_sat_logic(self, a: Assignments) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < self.0@.len() &&
                self.0@[i].lit_sat_logic(a)
        }
    }
}

impl Clause {
    #[requires(self.vars_in_range(a.0@.len()))]
    #[ensures(!result ==> !self.clause_sat_logic(*a))]
    #[ensures(result ==> self.clause_sat_logic(*a))]
    fn eval_clause(&self, a: &Assignments) -> bool {
        let mut i: usize = 0;
        let clause_len = self.0.len();
        #[invariant(forall<j: Int> 0 <= j && j < i@ ==> !self.0@[j].lit_sat_logic(*a))]
        #[invariant(i@ <= clause_len@)]
        while i < clause_len {
            if self.0[i].lit_sat(a) {
                return true;
            }
            i += 1;
        }
        false
    }
}

impl Formula {
    #[requires(self.invariant())]
    #[requires(a.0@.len() == self.num_vars@)]
    #[ensures(result == self.sat(*a))]
    fn eval_formula(&self, a: &Assignments) -> bool {
        let mut i: usize = 0;
        #[invariant(forall<j: Int> 0 <= j && j < i@ ==> self.clauses@[j].clause_sat_logic(*a))]
        while i < self.clauses.len() {
            if !self.clauses[i].eval_clause(a) {
                return false;
            }
            i += 1;
        }
        true
    }
}

#[requires(pa.ix@ < pa.assign.0@.len())]
#[requires(pa.assign.0@.len() <= usize::MAX@)]
#[requires(pa.invariant(pa.assign@.len()))]
#[requires(b@ < 2)]
#[ensures(result.invariant(pa.assign@.len()))]
#[ensures(result.assign.compatible(*pa))]
#[ensures(result.assign.0@[pa.ix@] == b)]
#[ensures(result.ix@ == pa.ix@ + 1)]
fn set_next(pa: &Pasn, b: AssignedState) -> Pasn {
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
        return f.eval_formula(&pa.assign);
    }
    solve(f, set_next(&pa, 1)) || solve(f, set_next(&pa, 0))
}

#[requires(f.invariant())]
#[ensures(!result ==> forall<a: Assignments> a.0@.len() == f.num_vars@ && a.invariant()
                  ==> !f.sat(a))]
#[ensures( result ==> exists<a: Assignments> f.sat(a))]
pub fn solver(f: &Formula) -> bool {
    solve(f, Pasn { assign: Assignments(vec![0; f.num_vars]), ix: 0 })
}
