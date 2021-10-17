// WHY3PROVE
#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]
#![feature(type_ascription)]

extern crate creusot_contracts;

use creusot_contracts::*;

struct Vec<T>(std::vec::Vec<T>);

pub struct Ghost<T>
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
        Ghost::<T>
    }
}

impl<T: ?Sized> Model for Vec<T> {
    type ModelTy = Seq<T>;
    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        panic!()
    }
}

impl<T> Vec<T> {
    #[trusted]
    #[ensures(result.into() === (@self).len())]
    fn len(&self) -> usize {
        self.0.len()
    }

    #[trusted]
    #[ensures(result.into() === (@self).len())]
    fn len_u32(&self) -> u32 {
        self.0.len() as u32
    }

    #[trusted]
    #[ensures(match result {
        Some(t) => *t === (@*self).index(ix.into()),
        None => (@*self).len() <= ix.into(),
    })]
    fn get(&self, ix: usize) -> Option<&T> {
        self.0.get(ix)
    }

    #[trusted]
    #[ensures(@^self === (@self).push(v))]
    fn push(&mut self, v: T) {
        self.0.push(v)
    }

    #[trusted]
    #[requires(@ix < (@self).len())]
    #[ensures(*result === (@self).index(@ix))]
    fn index(&self, ix: usize) -> &T {
        use std::ops::Index;
        self.0.index(ix)
    }

    #[trusted]
    #[requires(@ix < (@*self).len())]
    #[ensures(*result === (@self).index(ix.into()))]
    #[ensures(^result === (@^self).index(ix.into()))]
    #[ensures(forall<j : Int> 0 <= j && j <= (@^self).len() ==>
        !(j === @ix) ==>
        (@^self).index(j) === (@*self).index(j))]
    #[ensures((@*self).len() === (@^self).len())]
    fn index_mut(&mut self, ix: usize) -> &mut T {
        use std::ops::IndexMut;
        self.0.index_mut(ix)
    }
}

fn main() {}

struct Assignment(Vec<bool>);
struct Lit { var: usize, value: bool }
struct Clause(Vec<Lit>);
struct Pasn { assign: Vec<bool>, ix: usize }
pub struct Formula { clauses: Vec<Clause>,  num_vars: usize }

#[predicate]
fn vars_in_range(n: Int, c: Clause) -> bool {
    pearlite! {
        forall<i : Int> 0 <= i && i < (@(c.0)).len() ==>
        0 <= @((@(c.0)).index(i)).var &&
        @((@(c.0)).index(i)).var < n
    }
}

#[predicate]
fn compatible(pa: &Pasn, a: Assignment) -> bool {
    pearlite! {
        (@(pa.assign)).len() === (@(a.0)).len() &&
        true // pa.assign[..pa.ix] == a[..pa.ix] // AKA deep equality
    }
}

#[predicate]
fn formula_invariant(f: &Formula) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < (@(f.clauses)).len() ==>
        vars_in_range(@(f.num_vars), ((@(f.clauses)).index(i)))
    }
}

fn complete(pa: &Pasn) -> bool {
    pa.ix == pa.assign.len()
}

#[requires(vars_in_range((@(a.0)).len(), *c))]
fn interp_clause(a: &Assignment, c: &Clause) -> bool {
    let mut i = 0;
    let clause_len = c.0.len();
    /*
    #[invariant(
        previous, forall<j: usize> 0usize <= j && j < i ==>
        (@(a.0)).index((@((@(c.0)).index(@j).var))) !=
        (@(c.0)).index(@j).value
        )]
    */
    #[invariant(loop_invariant, 0usize <= i && i <= clause_len)]
    while i < clause_len {
        let l = *a.0.index(c.0.index(i).var);
        let r = c.0.index(i).value;
        if !(l && r) && !(!l && !r) {
            return true;
        }
        i += 1;
    }
    false
}

#[requires(formula_invariant(f))]
#[ensures(formula_invariant(f))]
#[requires((@(a.0)).len() === @f.num_vars)]
fn interp_formula(a: &Assignment, f: &Formula) -> bool {
    let mut i = 0;
    let clauses_len = f.clauses.len();
    /*
    #[invariant(
        previous, forall<j: usize> 0usize <= j && j < i ==>
        (@(a.0)).index((@((@(c.0)).index(@j).var))) !=
        (@(c.0)).index(@j).value
        )]
    */
    #[invariant(loop_invariant, 0usize <= i && i <= clauses_len)]
    while i < clauses_len {
        if !interp_clause(a, &f.clauses.index(i)) {
            return false;
        }
        i += 1;
    }
    true
}

#[requires(@(pa.ix) < (@(pa.assign)).len())]
#[requires((@(pa.assign)).len() < 1000)] // just to ensure boundedness
#[requires(!(@(pa.ix) === (@(pa.assign)).len()))] // !complete
//#[ensures(compatible(pa, Assignment(result.assign)))]
fn set_true(pa: &Pasn) -> Pasn {
    let mut new_assign = Vec(vec![false;0]);
    let mut i = 0;
    let pa_len = pa.assign.len();
    #[invariant(loop_invariant, 0usize <= i && i <= pa_len)]
    while i < pa_len {
        if i == pa.ix {
            new_assign.push(true);
        } else {
            new_assign.push(*pa.assign.index(i));
        }
        i += 1;
    }
//    *new_assign.index_mut(pa.ix) = true; // doesnt prove
    Pasn { assign: new_assign, ix: pa.ix + 1 }
}




#[requires((@(pa.assign)).len() < 1000)]
#[requires(@(pa.ix) < (@(pa.assign)).len())]
#[requires(!(@(pa.ix) === (@(pa.assign)).len()))] // !complete
fn set_false(pa: &Pasn) -> Pasn {
    let mut new_assign = Vec(vec![false;0]);
    let mut i = 0;
    let pa_len = pa.assign.len();
    #[invariant(loop_invariant, 0usize <= i && i <= pa_len)]
    while i < pa_len {
        if i == pa.ix {
            new_assign.push(false);
        } else {
            new_assign.push(*pa.assign.index(i));
        }
        i += 1;
    }
//    *new_assign.index_mut(pa.ix) = false; // doesnt prove
    Pasn { assign: new_assign, ix: pa.ix + 1 }
}

impl WellFounded for usize {}

#[requires(formula_invariant(f))]
#[ensures(formula_invariant(f))]
#[requires((@(f.clauses)).len() < 1000)] // just to ensure boundedness
#[requires(@(pa.ix) <= (@(pa.assign)).len())]
#[requires((@(pa.assign)).len() === @f.num_vars)]
//#[variant((f.num_vars) - (pa.ix))]
fn inner(f: &Formula, pa: Pasn) -> bool {
    if complete(&pa) {
        return interp_formula(&Assignment(pa.assign), f);
    } else {
        if inner(f, set_true(&pa)) {
            return true;
        } else {
            return inner(f, set_false(&pa));
        }
    }
}

#[requires(formula_invariant(f))]
#[ensures(formula_invariant(f))]
#[requires((@(f.clauses)).len() < 1000)] // just to ensure boundedness
pub fn solver(f: &Formula) -> bool {
    let assign = Vec(vec![false; f.num_vars]);
    let base = Pasn { assign: assign, ix: 0 };
    inner(f, base)
}
