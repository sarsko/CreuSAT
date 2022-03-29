extern crate creusot_contracts;
use creusot_contracts::*;

pub struct Lit {
    pub idx: usize,
    pub polarity: bool,
}

#[predicate]
pub fn no_duplicate_indexes_inner(s: Seq<Lit>) -> bool {
    /*
    pearlite! {
        forall<j: Int, k: Int> 0 <= j && j < s.len() &&
                0 <= k && k < j ==> !(@s[k].idx === @s[j].idx)
    }
    */
    pearlite! {
        forall<j: Int, k: Int> 0 <= j && j < s.len() &&
                k != j ==> !(@s[k].idx === @s[j].idx)
    }
}

#[logic]
#[requires((c).len() === 2)]
#[requires((c2).len() === (c).len())]
#[requires((c2).exchange(c, 0, 1))]
#[requires(no_duplicate_indexes_inner(c))]
#[ensures(no_duplicate_indexes_inner(c2))]
pub fn lemma_permut_clause_no_dups(c: Seq<Lit>, c2: Seq<Lit>) {}