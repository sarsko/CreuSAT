// WHY3PROVE
#![feature(register_tool, rustc_attrs)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]
#![feature(type_ascription)]

extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

fn main() {}

struct Assignment(Vec<bool>);
struct Lit { var: usize, value: bool }
struct Clause(Vec<Lit>);
struct Pasn { assign: Vec<bool>, ix: usize }
pub struct Formula { clauses: Vec<Clause>,  num_vars: usize }

//impl WellFounded for usize {}

#[predicate]
fn vars_in_range(n: Int, c: Clause) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < (@(c.0)).len() ==>
        0 <= @((@(c.0))[i]).var &&
        @((@(c.0))[i]).var < n
    }
}

#[predicate]
fn compatible(pa: Pasn, a: Assignment) -> bool {
    pearlite! {
        (@(pa.assign)).len() === (@(a.0)).len() &&
        forall<i: usize> 0usize <= i && @i < @(pa.ix) ==>
        (@(pa.assign))[@i] === (@(a.0))[@i]
    }
}


#[predicate]
fn formula_invariant(f: &Formula) -> bool {
    pearlite! {
        forall<i: usize> 0usize <= i && @i < (@(f.clauses)).len() ==>
        vars_in_range(@(f.num_vars), ((@(f.clauses))[@i]))
    }
}


#[predicate]
fn not_sat_clause(a: Assignment, c: Clause) -> bool {
    pearlite! {
        forall<i: usize> 0usize <= i && @i < (@(c.0)).len() ==>
        ((@(a.0))[@(((@(c.0))[@i]).var)]) !=
        (((@(c.0))[@i]).value)
    }
}

#[predicate]
fn sat_formula(a: Assignment, f: &Formula) -> bool {
    pearlite! {
        forall<i: usize> 0usize <= i && @i < (@(f.clauses)).len() ==>
        !not_sat_clause(a, (@(f.clauses))[@i])
    }
}

#[trusted]
#[ensures(result === true ==> (l === r))]
#[ensures(result === false ==> (l != r))]
#[ensures(result === (l === r))]
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
        (@(a.0))[(@((@(c.0))[@j].var))] !=
        (@(c.0))[@j].value
    )]
    #[invariant(loop_invariant, 0usize <= i && i <= clause_len)]
    while i < clause_len {
        let l = a.0[c.0[i].var];
        let r = c.0[i].value;
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
        !(not_sat_clause(*a, (@(f.clauses))[@j]))
    )]
    #[invariant(loop_invariant, 0usize <= i && i <= clauses_len)]
    while i < clauses_len {
        if !interp_clause(a, &f.clauses[i]) {
            return false;
        }
        i += 1;
    }
    true
}

#[trusted]
#[ensures(
    forall<i: Int> 0 <= i && i < (@pa.assign).len() ==>
    (@pa.assign)[i] === (@result)[i]
)]
#[ensures((@pa.assign).len() === (@result).len())]
fn clone(pa: &Pasn) -> Vec<bool> {
    //pa.assign.clone();
    panic!();
}

#[requires(@(pa.ix) < (@(pa.assign)).len())]
#[requires(!(@(pa.ix) === (@(pa.assign)).len()))] // !complete
#[ensures(compatible(*pa, Assignment(result.assign)))]
#[ensures(((@(result.assign))[@(pa.ix)]) === true)]
#[ensures(result.ix === pa.ix + 1usize)]
fn set_true(pa: &Pasn) -> Pasn {
    let pa_len = pa.assign.len();
    let mut new_assign = clone(pa);
    new_assign[pa.ix] = true;
    Pasn { assign: new_assign, ix: pa.ix + 1 }
}

#[requires(@(pa.ix) < (@(pa.assign)).len())]
#[requires(!(@(pa.ix) === (@(pa.assign)).len()))] // !complete
#[ensures(((@(result.assign))[@(pa.ix)]) === false)]
#[ensures(compatible(*pa, Assignment(result.assign)))]
#[ensures(result.ix === pa.ix + 1usize)]
fn set_false(pa: &Pasn) -> Pasn {
    let pa_len = pa.assign.len();
    let mut new_assign = clone(pa);
    new_assign[pa.ix] = false;
    Pasn { assign: new_assign, ix: pa.ix + 1 }
}


#[requires(formula_invariant(f))]
#[ensures(formula_invariant(f))]
#[requires(@(pa.ix) <= (@(pa.assign)).len())]
#[requires((@(pa.assign)).len() === @f.num_vars)]
//#[variant((f.num_vars) - (pa.ix))]
#[ensures(
    result === false ==> forall<a: Assignment> compatible(pa, a) ==>
    !sat_formula(a, f)
)]
#[ensures(result === true ==> exists<a: Assignment> sat_formula(a,f))]
fn inner(f: &Formula, pa: Pasn) -> bool {
    if pa.ix == pa.assign.len() { // Could be extracted to `complete`
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
    result === true ==> f.num_vars == 0usize || exists<a: Assignment> sat_formula(a, f))]
#[requires((@(f.clauses)).len() < 10000)] // just to ensure boundedness
#[requires(formula_invariant(f))]
#[ensures(formula_invariant(f))]
pub fn solver(f: &Formula) -> bool {
    if f.num_vars == 0 {
        return true;
    }
    let mut assign: Vec<bool> = Vec::new();
    let mut i = 0;
    #[invariant(loop_invariant, 0usize <= i && i <= f.num_vars)]
    #[invariant(leng_invariant, (@assign).len() === @i)]
    while i < f.num_vars {
        assign.push(false);
        i += 1
    }
    let base = Pasn { assign: assign, ix: 0 };
    inner(f, base)
}