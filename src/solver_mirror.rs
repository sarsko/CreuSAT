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

    // TODO: This makes Vec.clone() unusable in regular Rust
    #[trusted]
    #[ensures(
        forall<i: Int> 0 <= i && i < (@self).len() ==>
        (@self).index(i) === (@result).index(i)
    )]
    #[ensures((@self).len() === (@result).len())]
    fn clone(&self) -> Self {
        panic!()
    }

}

/*
impl<T: std::clone::Clone> Clone for Vec<T> {
}
*/

fn main() {}

struct Assignment(Vec<bool>);
struct Lit { var: usize, value: bool }
struct Clause(Vec<Lit>);
struct Pasn { assign: Vec<bool>, ix: usize }
pub struct Formula { clauses: Vec<Clause>,  num_vars: usize }

impl WellFounded for usize {}

#[predicate]
fn vars_in_range(n: Int, c: Clause) -> bool {
    pearlite! {
        forall<i : Int> 0 <= i && i < (@(c.0)).len() ==>
        0 <= @((@(c.0)).index(i)).var &&
        @((@(c.0)).index(i)).var < n
    }
}

#[predicate]
fn compatible(pa: Pasn, pa2: Pasn) -> bool {
    pearlite! {
        (@(pa.assign)).len() === (@(pa2.assign)).len() &&
        forall<i: usize> 0usize <= i && @i < @(pa.ix) ==>
        (@(pa.assign)).index(@i) === (@(pa2.assign)).index(@i)
    }
}

#[predicate]
fn compatible_a(pa: Pasn, a: Assignment) -> bool {
    pearlite! {
        (@(pa.assign)).len() === (@(a.0)).len() &&
        forall<i: usize> 0usize <= i && @i < @(pa.ix) ==>
        (@(pa.assign)).index(@i) === (@(a.0)).index(@i)
    }
}

/*
#[logic]
fn lemma_complete_compat() -> bool {
    pearlite! {
        forall<pa: Pasn> 0 <= 0 ==>
            forall<a: Assignment> compatible_a(pa, a) ==>
            (@pa.ix === (@(pa.assign)).len()) ==> pa.assign === a.0
    }
}
*/

#[predicate]
fn formula_invariant(f: &Formula) -> bool {
    pearlite! {
        forall<i: usize> 0usize <= i && @i < (@(f.clauses)).len() ==>
        vars_in_range(@(f.num_vars), ((@(f.clauses)).index(@i)))
    }
}

/*
#[predicate]
fn sat_clause(a: &Assignment, c: Clause) -> bool {
    pearlite! {
        exists<i: Int> 0 <= i && i < (@(c.0)).len() ==>
        ((@(a.0)).index(@(((@(c.0)).index(i)).var))) ===
        (((@(c.0)).index(i)).value)
    }
}
*/

#[predicate]
fn not_sat_clause(a: Assignment, c: Clause) -> bool {
    pearlite! {
        forall<i: usize> 0usize <= i && @i < (@(c.0)).len() ==>
        ((@(a.0)).index(@(((@(c.0)).index(@i)).var))) !=
        (((@(c.0)).index(@i)).value)
    }
}

#[predicate]
fn sat_formula(a: Assignment, f: &Formula) -> bool {
    pearlite! {
        forall<i: usize> 0usize <= i && @i < (@(f.clauses)).len() ==>
        !not_sat_clause(a, (@(f.clauses)).index(@i))
    }
}

#[trusted]
#[ensures(result === true ==> (l === r))]
#[ensures(result === false ==> (l != r))]
#[ensures(result === (l == r))]
fn eqb(l: bool, r: bool) -> bool {
    l == r
}

#[requires(vars_in_range((@(a.0)).len(), *c))]
#[ensures(vars_in_range((@(a.0)).len(), *c))]
#[ensures(result === !not_sat_clause(*a, *c))]
#[ensures(result === false ==> not_sat_clause(*a, *c))]
#[ensures(result === true ==> !not_sat_clause(*a, *c))]
fn interp_clause(a: &Assignment, c: &Clause) -> bool {
    let mut i = 0;
    let clause_len = c.0.len();
    #[invariant(
        previous, forall<j: usize> 0usize <= j && j < i ==>
        (@(a.0)).index((@((@(c.0)).index(@j).var))) !=
        (@(c.0)).index(@j).value
    )]
    #[invariant(loop_invariant, 0usize <= i && i <= clause_len)]
    while i < clause_len {
        let l = *a.0.index(c.0.index(i).var);
        let r = c.0.index(i).value;
        if eqb(l, r) {
            return true;
        }
        i += 1;
    }
    false
}

#[requires(formula_invariant(f))]
#[ensures(formula_invariant(f))]
#[ensures(result === false ==> !sat_formula(*a, f))]
#[ensures(result === true ==> sat_formula(*a, f))]
#[requires((@(a.0)).len() === @f.num_vars)]
fn interp_formula(a: &Assignment, f: &Formula) -> bool {
    let mut i = 0;
    let clauses_len = f.clauses.len();
    #[invariant(previous,
        forall<j: usize> 0usize <= j && j < i ==>
        !(not_sat_clause(*a, (@(f.clauses)).index(@j)))
    )]
    #[invariant(loop_invariant, 0usize <= i && i <= clauses_len)]
    while i < clauses_len {
        if !interp_clause(a, f.clauses.index(i)) {
            return false;
        }
        i += 1;
    }
    true
}

#[requires(@(pa.ix) < (@(pa.assign)).len())]
#[requires(!(@(pa.ix) === (@(pa.assign)).len()))] // !complete
#[ensures(compatible_a(*pa, Assignment(result.assign)))]
#[ensures(((@(result.assign)).index(@(pa.ix))) === true)]
#[ensures(result.ix === pa.ix + 1usize)]
fn set_true(pa: &Pasn) -> Pasn {
    let pa_len = pa.assign.len();
    let mut new_assign = pa.assign.clone();
    *new_assign.index_mut(pa.ix) = true;
    Pasn { assign: new_assign, ix: pa.ix + 1 }
}

#[requires(@(pa.ix) < (@(pa.assign)).len())]
#[requires(!(@(pa.ix) === (@(pa.assign)).len()))] // !complete
#[ensures(((@(result.assign)).index(@(pa.ix))) === false)]
#[ensures(compatible_a(*pa, Assignment(result.assign)))]
#[ensures(result.ix === pa.ix + 1usize)]
fn set_false(pa: &Pasn) -> Pasn {
    let pa_len = pa.assign.len();
    let mut new_assign = pa.assign.clone();
    *new_assign.index_mut(pa.ix) = false;
    Pasn { assign: new_assign, ix: pa.ix + 1 }
}


#[requires(formula_invariant(f))]
#[ensures(formula_invariant(f))]
#[requires(0 <= 0)] // Needed cus of #159
#[requires(@(pa.ix) <= (@(pa.assign)).len())]
#[requires((@(pa.assign)).len() === @f.num_vars)]
#[variant((f.num_vars) - (pa.ix))]
#[ensures(
    result === false ==> forall<a: Assignment> compatible_a(pa, a) ==>
    !sat_formula(a, f)
)]
#[ensures(result === true ==> exists<a: Assignment> 0 <= 0 ==> sat_formula(a,f))]
fn inner(f: &Formula, pa: Pasn) -> bool {
    if pa.ix == pa.assign.len() { // Should be extracted to `complete`
        return interp_formula(&Assignment(pa.assign), f);
    } else {
        if inner(f, set_true(&pa)) {
            return true;
        }
        else {
            return inner(f, set_false(&pa));
        }
    }
}

#[ensures(
    result === false ==> forall<a: Assignment> (@(a.0)).len() === @f.num_vars ==>
    !sat_formula(a, f)
)]
#[ensures(
    result === true ==> f.num_vars == 0usize || !(forall<a: Assignment> (@(a.0)).len() === @f.num_vars ==>
    !sat_formula(a, f))
)]
//#[ensures(result === true ==> exists<a: Assignment> f.num_vars > 0usize ==> !!sat_formula(a,f))]
#[requires((@(f.clauses)).len() < 10000)] // just to ensure boundedness
#[requires(formula_invariant(f))]
#[ensures(formula_invariant(f))]
pub fn solver(f: &Formula) -> bool {
    if f.num_vars == 0 {
        return true;
    }
    let mut assign: Vec<bool> = Vec(vec![]);
    let mut i = 0;
    #[invariant(loop_invariant, 0usize <= i && i < f.num_vars)]
    while i < f.num_vars {
        assign.push(false);
        i += 1
    }
    //let assign = Vec(vec![false; f.num_vars]); // turns out vec! is opaque
    let base = Pasn { assign: assign, ix: 0 };
    inner(f, base)
}
