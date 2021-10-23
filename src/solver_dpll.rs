// WHY3PROVE
#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]
#![feature(type_ascription)]

extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

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
/*

impl Vec<bool> {
    #[trusted]
    #[ensures(
        forall<i: Int> 0 <= i && i < (@self).len() ==>
        (@self)[i] === (@result)[i]
    )]
    #[ensures((@self).len() === (@result).len())]
    fn clone(&self) -> Self {
        panic!();
        //Vec(self.0.clone()) // .0 has become private
    }
}
*/

fn main() {}

struct Lit { idx: usize, positive: bool }
struct Clause(Vec<Lit>);
pub struct Formula { clauses: Vec<Clause>, num_vars: usize }

#[predicate]
fn vars_in_range(n: Int, c: Clause) -> bool {
    pearlite! {
        forall<i: usize> 0usize <= i && @i < (@(c.0)).len() ==>
            (0 <= @((@(c.0))[@i]).idx &&
        @((@(c.0))[@i]).idx < n)
    }
}

#[predicate]
fn formula_invariant(f: &Formula) -> bool {
    pearlite! {
        (forall<i: usize> 0usize <= i && @i < (@(f.clauses)).len() ==>
        vars_in_range(@(f.num_vars), ((@(f.clauses))[@i])))
    }
}

#[predicate]
fn index_invariant(l: Lit, v: Vec<bool>) -> bool {
    pearlite! {
        0 <= 0 && @(l.idx) < (@v).len()
    }
}

#[predicate]
fn clause_invariant(c: Clause, v: Vec<bool>) -> bool {
    pearlite! {
        forall<i: usize> 0usize <= i && @i < (@c.0).len() ==>
            index_invariant((@c.0)[@i], v)
    }
}

impl WellFounded for usize {}

#[trusted]
#[ensures(result === true ==> (l === r))]
#[ensures(result === false ==> (l != r))]
#[ensures(result === (l === r))]
fn eqb(l: bool, r: bool) -> bool {
    l == r
}

// TODO: Reconsider function(i.e. make it generic / move it)
#[ensures((@result).len() === @n)]
fn make_vec_of_size(n: usize) -> Vec<bool>{
    let mut out: Vec<bool> = Vec::new();
    if n == 0 {
        return out;
    }
    #[invariant(loop_invariant, (@out).len() <= @n)]
    while out.len() < n {
        out.push(false);
    }
    return out;
}

#[requires(index_invariant(*literal, *neg))]
#[requires(index_invariant(*literal, *pos))]
#[ensures(index_invariant(*literal, ^neg))]
#[ensures(index_invariant(*literal, ^pos))]
#[ensures(index_invariant(*literal, *neg))]
#[ensures(index_invariant(*literal, *pos))]
#[ensures((@*pos).len() === (@^pos).len())]
#[ensures((@*neg).len() === (@^neg).len())]
fn consistent_literal(literal: &Lit, pos: &mut Vec<bool>, neg: &mut Vec<bool>) -> bool {
    if eqb(literal.positive, true) {
        if eqb(*neg.index(literal.idx), true) {
            return false;
        } else {
            *pos.index_mut(literal.idx) = true;
        }
    } else {
        if eqb(*pos.index(literal.idx), true) {
            return false;
        } else {
            *neg.index_mut(literal.idx) = true;
        }
    }
    return true;
}


/*
#[requires(vars_in_range((@pos).len(), *c))] // this wont prove higher up ?
#[requires(vars_in_range((@neg).len(), *c))]
*/
#[ensures(vars_in_range((@^pos).len(), *c))]
#[ensures(vars_in_range((@^neg).len(), *c))]
/*
#[requires((@pos).len() === (@neg).len())]
#[ensures((@pos).len() === (@neg).len())]
*/
#[ensures((@*pos).len() === (@^pos).len())]
#[ensures((@*neg).len() === (@^neg).len())]
#[requires(
    forall<i: usize> 0usize <= i && @i < (@c.0).len() ==>
    index_invariant((@c.0)[@i], *neg))]
/*
// Adding this makes it not prove higher up, but it is not needed?
#[requires(
    forall<i: usize> 0usize <= i && @i < (@c.0).len() ==>
    index_invariant((@c.0)[@i], *pos))]
*/
#[ensures(
    forall<i: usize> 0usize <= i && @i < (@c.0).len() ==>
    index_invariant((@c.0)[@i], ^neg))]
#[ensures(
    forall<i: usize> 0usize <= i && @i < (@c.0).len() ==>
    index_invariant((@c.0)[@i], ^pos))]
// Doesnt wanna prove for some reason (should be same as above)
/*
#[requires(clause_invariant(*c, *pos))]
#[requires(clause_invariant(*c, *neg))]
#[ensures(clause_invariant(*c, ^pos))]
#[ensures(clause_invariant(*c, ^neg))]
*/

//#[requires(index_invariant(*literal, *pos))]
//
fn consistent_clause(c: &Clause, pos: &mut Vec<bool>, neg: &mut Vec<bool>) -> bool {
    let mut i = 0;
    let clause_len = c.0.len();
    let pos_len = pos.len(); // these should be ghost
    let neg_len = neg.len();
    let old_p = Ghost::record(&pos);
    let old_n = Ghost::record(&neg);
    #[invariant(neg_invariant,
        forall<i: usize> 0usize <= i && @i < (@c.0).len() ==>
        index_invariant((@c.0)[@i], *neg))]
    #[invariant(pos_invariant,
        forall<i: usize> 0usize <= i && @i < (@c.0).len() ==>
        index_invariant((@c.0)[@i], *pos))]
    /*
    #[invariant(pos_invariant, clause_invariant((*c), *pos))]
    #[invariant(neg_invariant, clause_invariant((*c), *neg))]
    */
    #[invariant(proph_pos, ^pos === ^@old_p)]
    #[invariant(proph_neg, ^neg === ^@old_n)]
    #[invariant(same_pos, (@*pos).len() === (@*@old_p).len())]
    #[invariant(same_neg, (@*neg).len() === (@*@old_n).len())]
    #[invariant(same_len, (@*pos).len() === @pos_len)]
    #[invariant(same_len2, (@*neg).len() === @neg_len)]
    #[invariant(loop_bound, 0usize <= i && i <= clause_len)]
    while i < clause_len {
        let literal = c.0.index(i);
        if !consistent_literal(literal, pos, neg) {
            return false;
        }
        i += 1;
    }
    return true;
}


#[requires((@(f.clauses)).len() < 10000)] // just to ensure boundedness
#[requires(formula_invariant(f))]
#[ensures(formula_invariant(f))]
fn consistent(f: &Formula) -> bool {
    let mut positives: Vec<bool> = make_vec_of_size(f.num_vars);
    let mut negatives: Vec<bool> = make_vec_of_size(f.num_vars);
    let clauses_len = f.clauses.len();
    let mut i = 0;
    /*
    #[invariant(neg_invariant,
        forall<i: usize> 0usize <= i && i < clauses_len ==>
        clause_invariant((@(f.clauses))[@i], negatives))]
    */
    #[invariant(neg_invariant,
        forall<k: usize> 0usize <= k && k < clauses_len ==>
        forall<j: usize> 0usize <= j && @j < (@(((@(f.clauses))[@k]).0)).len() ==>
        index_invariant((@(((@(f.clauses))[@k]).0))[@j], negatives))]
    #[invariant(pos_invariant,
        forall<k: usize> 0usize <= k && k < clauses_len ==>
        forall<j: usize> 0usize <= j && @j < (@(((@(f.clauses))[@k]).0)).len() ==>
        index_invariant((@(((@(f.clauses))[@k]).0))[@j], positives))]
    #[invariant(loop_bound, 0usize <= i && i <= clauses_len)]
    #[invariant(pos, forall<k: usize> 0usize <= k && k < clauses_len ==>
        vars_in_range((@positives).len(), (@(f.clauses))[@k]))]
    #[invariant(neg, forall<k: usize> 0usize <= k && k < clauses_len ==>
        vars_in_range((@negatives).len(), (@(f.clauses))[@k]))]
    while i < clauses_len {
        let clause = &f.clauses.index(i);
        if !consistent_clause(clause, &mut positives, &mut negatives) {
            return false;
        }
        i += 1;
    }
    return true;
}

#[requires((@(f.clauses)).len() < 10000)] // just to ensure boundedness
#[requires(formula_invariant(f))]
#[ensures(formula_invariant(f))]
fn contains_empty(f: &Formula) -> bool {
    let mut i = 0;
    let clauses_len = f.clauses.len();
    #[invariant(loop_bound, i <= clauses_len)]
    while i < clauses_len {
        let clause = &f.clauses.index(i).0;
        if clause.len() == 0 {
            return true;
        }
        i += 1;
    }
    return false;
}

#[requires((@(f.clauses)).len() < 10000)] // just to ensure boundedness
#[requires(formula_invariant(f))]
#[ensures(formula_invariant(f))]
fn inner(f: &Formula) -> bool {
    if contains_empty(f) {
        return false;
    }
    if consistent(f) {
        return true;
    }
    return false;
    /*
    let literal = choose_literal(&clauses, clause_counter);
    let new_counter = clause_counter + 1;
    let mut clauses = set_literals(clauses, literal);
    let mut clauses2 = set_literals(clauses, literal);
    set_literals(&mut clauses2, -literal);
    return dpll(&mut clauses, new_counter, num_literals) || dpll(&mut clauses2, new_counter, num_literals);
    */
}

#[requires((@(f.clauses)).len() < 10000)] // just to ensure boundedness
#[requires(formula_invariant(f))]
#[ensures(formula_invariant(f))]
pub fn solver(f: &Formula) -> bool {
    if f.num_vars == 0 {
        return true;
    }
    inner(f)
}
