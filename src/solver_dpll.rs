// WHY3PROVE
#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]
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

#[derive(Copy)]
struct Lit { idx: usize, positive: bool }
struct Clause(Vec<Lit>);
pub struct Formula { clauses: Vec<Clause>, num_vars: usize, cntr: usize }

// TODO: Make this actual code
impl Clause {
    #[trusted]
    #[ensures(
        forall<i: Int> 0 <= i && i < (@self.0).len() ==>
        (@self.0)[i] === (@result.0)[i]
    )]
    #[ensures((@self.0).len() === (@result.0).len())]
    fn clone(&self) -> Self {
        panic!();
        //Clause(self.0.clone())
    }

    #[ensures(result === false ==>
        forall<i: Int> 0 <= i && i < (@self.0).len() ==>
        @((@self.0)[i].idx) != @(l.idx))]
    #[ensures(result === true ==>
        exists<i: Int> 0 <= i && i < (@self.0).len() ==>
        @((@self.0)[i].idx) === @(l.idx))]
    fn contains_ignore_polarity(&self, l: &Lit) -> bool {
        let len = self.0.len();
        let mut i = 0;
        #[invariant(loop_bound, i <= len)]
        #[invariant(previous,
            forall<j: Int> 0 <= j && j < @i ==>
            @((@self.0)[j].idx) != @(l.idx))]
        while i < len {
            let lit = self.0.index(i);
            if lit.idx == l.idx {
                return true;
            }
            i += 1;
        }
        return false;
    }

    #[ensures(result === false ==>
        forall<i: Int> 0 <= i && i < (@self.0).len() ==>
        (@((@self.0)[i].idx) != @(l.idx) ||
        ((@self.0)[i].positive) != (l.positive)))]
    #[ensures(result === true ==>
        exists<i: Int> 0 <= i && i < (@self.0).len() ==>
        (@((@self.0)[i].idx) === @(l.idx) &&
        ((@self.0)[i].positive) === (l.positive)))]
    fn contains(&self, l: &Lit) -> bool {
        let len = self.0.len();
        let mut i = 0;
        #[invariant(loop_bound, i <= len)]
        #[invariant(previous,
            forall<j: Int> 0 <= j && j < @i ==>
            @((@self.0)[j].idx) != @(l.idx) ||
        ((@self.0)[j].positive) != (l.positive))]
        while i < len {
            let lit = self.0.index(i);
            if lit.idx == l.idx && lit.positive == l.positive {
                return true;
            }
            i += 1;
        }
        return false;
    }
}
impl Formula {
    #[trusted]
    #[ensures(
        forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
        (@self.clauses)[i] === (@result.clauses)[i]
    )]
    #[ensures((@self.clauses).len() === (@result.clauses).len())]
    fn clone(&self) -> Self {
        panic!();
        //Clause(self.0.clone())
    }
}

impl Lit {
    #[trusted]
    #[ensures(@result.idx === @self.idx && result.positive === self.positive)]
    fn clone(&self) -> Self {
        panic!();
        //Clause(self.0.clone())
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
fn formula_invariant2(c: Vec<Clause>, n: usize) -> bool {
    pearlite! {
        (forall<i: usize> 0usize <= i && @i < (@(c)).len() ==>
        vars_in_range(@(n), ((@(c))[@i])))
    }
}

#[predicate]
fn formula_invariant(f: Formula) -> bool {
    pearlite! {
        @f.cntr <= (@f.clauses).len() &&
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
    /*
    #[invariant(pos_invariant,
        forall<i: usize> 0usize <= i && @i < (@c.0).len() ==>
        index_invariant((@c.0)[@i], *pos))]
    */
    #[invariant(pos_invariant,
        forall<i: Int> 0 <= i && i < (@c.0).len() ==>
        index_invariant((@c.0)[i], *pos))]
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
#[requires(formula_invariant(*f))]
#[ensures(formula_invariant(*f))]
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

#[requires(formula_invariant(*f))]
#[ensures(formula_invariant(*f))]
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

// TODO: Fix the vars_in range post. No idea why it doesnt prove
#[requires(formula_invariant(*f))]
#[ensures(formula_invariant(*f))]
#[requires(vars_in_range(@(f.num_vars), *clause))]
#[ensures(vars_in_range(@(f.num_vars), result))]
/*
#[ensures(
        forall<i: usize> 0usize <= i && @i < (@(result.0)).len() ==>
            (0 <= @((@(result.0))[@i]).idx &&
        @((@(result.0))[@i]).idx < @f.num_vars))]
*/
fn copy_clause_without(f: &Formula, clause: &Clause, literal: &Lit) -> Clause {
    let mut out_clause = Clause(Vec::new());
    let mut j = 0;
    /*
    #[invariant(maintain2,
        forall<i: usize> 0usize <= i && @i < (@(out_clause.0)).len() ==>
            (0 <= @((@(out_clause.0))[@i]).idx &&
        @((@(out_clause.0))[@i]).idx < @f.num_vars))]
    */
    #[invariant(maintain_invariant, vars_in_range(@(f.num_vars), out_clause))]
    #[invariant(loop_bound, @j <= (@clause.0).len())]
    while j < clause.0.len() {
        let lit = clause.0.index(j);
        if lit.idx != literal.idx {
            //let new_lit = Lit{idx: lit.idx, positive: lit.positive};
            let new_lit = lit.clone();
            //out_clause.0.push(*lit);
            out_clause.0.push(new_lit);
        }
        j += 1;
    }
    return out_clause;
}

#[requires(formula_invariant(*f))]
#[ensures(formula_invariant(*f))]
#[ensures(formula_invariant2(result, f.num_vars))]
//#[ensures((forall<i: usize> 0usize <= i && @i < (@(f.clauses)).len() ==>
//        vars_in_range(@(f.num_vars), ((@(result))[@i]))))]
fn unit_propagate(f: &Formula, literal: &Lit) -> Vec<Clause> {
    let mut out_clauses: Vec<Clause> = Vec::new();
    let mut i = 0;
    #[invariant(loop_bound, @i <= (@f.clauses).len())]
    /*
    #[invariant(maintain_invariant,
        forall<j: usize> j < i ==>
            vars_in_range(@(f.num_vars), ((@(out_clauses))[@j])))]
    */
    #[invariant(mi, formula_invariant2(out_clauses, f.num_vars))]
    while i < f.clauses.len() {
        let clause = f.clauses.index(i);
        if !clause.contains(&literal) {
            //let new_clause = copy_clause_without(f, clause, literal);
            let new_clause = clause.clone();
            out_clauses.push(new_clause);
        }
        i += 1;
    }
    return out_clauses;
}

#[requires(formula_invariant(*f))]
#[ensures(formula_invariant(^f))]
fn check_and_propagate(f: &mut Formula) -> bool {
    let mut i = 0;
    #[invariant(loop_bound, @i <= (@f.clauses).len())]
    #[invariant(maintain_invariant, formula_invariant(*f))]
    while i < f.clauses.len() {
        if f.clauses.index(i).0.len() == 1 {
            f.clauses = unit_propagate(f, f.clauses.index(i).0.index(0));
            return false;
        }
        i += 1;
    }
    return true;
}

#[requires(formula_invariant(*f))]
#[ensures(formula_invariant(^f))]
fn do_unit_propagation(f: &mut Formula){
    let mut stabilized = false;
    while !stabilized {
        stabilized = check_and_propagate(f);
    }
}

#[requires(formula_invariant(*f))]
#[ensures(formula_invariant(^f))]
#[requires(@f.cntr < 2000_000_000)] // TODO: This shouldnt be needed
#[requires(@f.cntr < (@(f.clauses)).len())]
fn next_literal(f: &mut Formula) -> usize {
    let out = f.cntr;
    f.cntr = f.cntr + 1;
    return out;
}

#[requires((@(f.clauses)).len() < 10000)] // just to ensure boundedness
#[requires(@f.cntr < 2000000)] // TODO: This shouldnt be needed
#[requires(formula_invariant(*f))]
#[ensures(formula_invariant(^f))]
fn inner(f: &mut Formula) -> bool {
    if contains_empty(f) {
        return false;
    }
    if consistent(f) {
        return true;
    }
    do_unit_propagation(f);
    let literal = next_literal(f);
    let mut f1 = f.clone();
    let mut f2 = f.clone();
    let pos_lit = Lit{idx: literal, positive: true};
    let neg_lit = Lit{idx: literal, positive: false};
    let mut pos_vec = Vec::new();
    pos_vec.push(pos_lit);
    let mut neg_vec = Vec::new();
    neg_vec.push(neg_lit);
    f1.clauses.push(Clause(pos_vec));
    f2.clauses.push(Clause(neg_vec));
    return inner(&mut f1) || inner(&mut f2); // TODO: Back to single cloning
}

#[requires((@(f.clauses)).len() < 10000)] // just to ensure boundedness
#[requires(@(f.cntr) == 0)]
#[requires(formula_invariant(*f))]
#[ensures(formula_invariant(^f))]
pub fn solver(f: &mut Formula) -> bool {
    if f.num_vars == 0 {
        return true;
    }
    inner(f)
}
