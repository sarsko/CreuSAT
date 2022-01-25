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
fn clause_unit(a: Seq<Option<bool>>, c: Seq<Lit>) -> bool {
    pearlite! {
        count_v(None, c, a, 0) === 1 && !sat_clause_inner(a, c)
    }
}

#[predicate]
fn clause_unit2(a: Seq<Option<bool>>, c: Seq<Lit>) -> bool {
    pearlite! {
        true // TODO
        //false_count(a, c) + 1 === c.len() && true_count(a, c) === 0
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
                    Some(b) => (@self)[i].polarity === b,
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

        forall<k: Option<bool>, c: Seq<Lit>, s: Seq<Option<bool>>, x: Option<bool>>
*/
// Not correct
#[logic]
fn lemma_count_v_cons() -> bool{
    pearlite! {
        forall<l: Lit, c: Seq<Lit>, s: Seq<Option<bool>>, x: Option<bool>>
        count_v(x, c, s, 0) === count_v(x, c.push(l), s, 0)
    }
}

        //count_v(k, c, s.push(k), 0) === 0
/*
#[logic]
fn count_v(v: Option<bool>, c: Seq<Lit>, a: Seq<Option<bool>>, j: Int) -> Int {
*/
/*
  lemma occ_cons:
    forall k: 'a, s: seq 'a, x: 'a.
    (occ_all k (cons x s) =
    if k = x then 1 + occ_all k s else occ_all k s
    ) by (cons x s == (cons x empty) ++ s)

  lemma occ_snoc:
    forall k: 'a, s: seq 'a, x: 'a.
    occ_all k (snoc s x) =
    if k = x then 1 + occ_all k s else occ_all k s

  lemma occ_tail:
    forall k: 'a, s: seq 'a.
    length s > 0 ->
    (occ_all k s[1..] =
    if k = s[0] then (occ_all k s) - 1 else occ_all k s
    ) by (s == cons s[0] s[1..])

  lemma append_num_occ:
    forall x: 'a, s1 s2: seq 'a.
    occ_all x (s1 ++ s2) =
    occ_all x s1 + occ_all x s2
*/

#[logic]
#[requires(forall<i: Int> 0 <= i && i < c.len() ==> @c[i].idx < a.len())]
#[requires(0 <= j && j <= c.len())]
#[variant(c.len() - j)]
fn count_v(v: Option<bool>, c: Seq<Lit>, a: Seq<Option<bool>>, j: Int) -> Int {
    if pearlite! { j === c.len() } {
        0
    } else if pearlite! { a[@c[j].idx] === v } {
       count_v(v, c, a, j+1) + 1
    } else {
       count_v(v, c, a, j+1)
    }
}

#[predicate]
fn idx_in(i: Int, c: Seq<Lit>) -> bool {
    pearlite! {
        exists<j: Int> 0 <= j && j < c.len() &&
            @c[j].idx === i
    }
}

#[logic]
// Duplis from lemma_unit_implies
#[requires(c.len() === c2.len())]
#[requires(0 <= i && i <= c.len())]
#[requires(forall<k: Int> 0 <= k && k < c.len() ==> @c[k].idx < a.len())]
#[requires(forall<k: Int> 0 <= k && k < c2.len() ==> @c2[k].idx < a.len())]
#[requires(a[@c[i].idx] === None && !(a[@c2[i].idx] === None))]
#[requires(c[i].idx != c2[i].idx)]
#[requires(forall<k: Int> 0 <= k && k < c.len() ==> k != i ==> c[k] === c2[k])]

#[variant(c.len() - j)]
#[requires(0 <= j && j <= c.len())]
#[ensures(result === count_v(None, c, a, j))]
#[ensures((j <= i) ==> count_v(None, c2, a, j) === (result - 1))] // Not checking out
#[ensures( (j > i) ==>  count_v(None, c2, a, j) === result)]
fn unit_aux(a: Seq<Option<bool>>, c: Seq<Lit>, c2: Seq<Lit>, i: Int, j: Int) -> Int {
    if pearlite! { j === c2.len() } {
        0
    } else if pearlite! { j === i } {
        unit_aux(a, c, c2, i, j+1) + 1
    } else if pearlite! { a[@c[j].idx] === None } {
        unit_aux(a, c, c2, i, j+1) + 1
    } else {
        unit_aux(a, c, c2, i, j+1)
    }
}

#[logic]
#[requires(c.len() === c2.len())]
#[requires(0 <= i && i <= c.len())]
#[requires(forall<k: Int> 0 <= k && k < c.len() ==> @c[k].idx < a.len())]
#[requires(forall<k: Int> 0 <= k && k < c2.len() ==> @c2[k].idx < a.len())]
#[requires(a[@c[i].idx] === None && !(a[@c2[i].idx] === None))]
#[requires(c[i].idx != c2[i].idx)]
#[requires(forall<k: Int> 0 <= k && k < c.len() ==> k != i ==> c[k] === c2[k])]
#[ensures(count_v(None, c2, a, 0) === count_v(None, c, a, 0) - 1)]
fn lemma_unit_implies(a: Seq<Option<bool>>, c: Seq<Lit>, c2: Seq<Lit>, i: Int) {
    pearlite! { unit_aux(a, c, c2, i, 0) };
}

#[logic]
#[requires(0 <= i && i < a.len())]
#[requires(a[i] === None)]
#[requires(@c[j].idx === i)]
#[ensures(occ_all(None, a.set(i, Some(true))) <= occ_all(None, a))] // Why isnt < OK?
#[ensures(a.set(i, Some(false))[i] === Some(false))]
fn false_assign_decreases(a: Seq<Option<bool>>, c: Seq<Lit>, i: Int, j: Int) {}

#[logic]
// Duplis from lemma_decreases_numof
#[requires(t.len() === t2.len())]
#[requires(0 <= i && i < t.len())]
#[requires(t[i] === v && !(t2[i] === v))]
#[requires(forall<k: Int> 0 <= k && k < t.len() ==> k != i ==> t[k] === t2[k])]

#[variant(t.len() - j)]
#[requires(0 <= j && j <= t.len())]
#[ensures(result === occ(v, t, j, t.len()))]
#[ensures( (j <= i) ==> occ(v, t2, j, t2.len()) === (result - 1))]
#[ensures( (j > i) ==> occ(v, t2, j, t2.len()) === result)]
fn numof_aux(v: Option<bool>, t: Seq<Option<bool>>, t2: Seq<Option<bool>>, i: Int, j: Int) -> Int {
    if pearlite! { j === t.len() } {
        0
    } else if pearlite! { j === i } {
        numof_aux(v, t, t2, i, j+1) + 1
    } else if pearlite! { t[j] === v } {
        numof_aux(v, t, t2, i, j+1) + 1
    } else {
        numof_aux(v, t, t2, i, j+1)
    }
}

#[logic]
#[requires(t.len() === t2.len())]
#[requires(0 <= i && i < t.len())]
#[requires(t[i] === v && !(t2[i] === v))]
#[requires(forall<j: Int> 0 <= j && j < t.len() ==> j != i ==> t[j] === t2[j])]
#[ensures(occ(v, t2, 0, t2.len()) === occ(v, t, 0, t.len()) - 1)]
fn lemma_decreases_numof(v: Option<bool>, t: Seq<Option<bool>>, t2: Seq<Option<bool>>, i: Int) {
    pearlite! { numof_aux(v, t, t2, i, 0) };
}

#[logic]
fn lemma_unitlemma(a: Seq<Option<bool>>, i: Int) {}




