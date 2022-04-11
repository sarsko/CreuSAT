extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

#[predicate]
pub fn sorted_range_rev(s: Seq<(usize, usize)>, l: Int, u: Int) -> bool {
    pearlite! {
        forall<i: Int, j: Int> l <= i && i < j && j < u ==> s[i].0 >= s[j].0
    }
}

#[predicate]
pub fn sorted_rev(s: Seq<(usize, usize)>) -> bool {
    pearlite! {
        sorted_range_rev(s, 0, s.len())
    }
}

#[predicate]
pub fn sorted_range(s: Seq<usize>, l: Int, u: Int) -> bool {
    pearlite! {
        forall<i: Int, j: Int> l <= i && i < j && j < u ==> s[i] <= s[j]
    }
}

#[predicate]
pub fn sorted(s: Seq<usize>) -> bool {
    pearlite! {
        sorted_range(s, 0, s.len())
    }
}

#[predicate]
pub fn partition_rev(v: Seq<(usize, usize)>, i: Int) -> bool {
    pearlite! { forall<k1 : Int, k2: Int> 0 <= k1 && k1 < i && i <= k2 && k2 < v.len() ==> v[k1].0 >= v[k2].0}
}

#[logic]
#[cfg_attr(all(any(trust_all, trust_logic), all(not(untrust_all), not(untrust_all_logic))), trusted)]
#[requires(s.len() > 0)]
#[ensures(result === s.subsequence(0, s.len() - 1))]
#[ensures(result.len() === s.len() - 1)]
#[ensures(forall<i: Int> 0 <= i && i < result.len() ==> result[i] === s[i])]
pub fn pop<T>(s: Seq<T>) -> Seq<T> {
    pearlite! {
        s.subsequence(0, s.len() - 1)
    }
}

#[logic]
#[cfg_attr(all(any(trust_all, trust_logic), all(not(untrust_all), not(untrust_all_logic))), trusted)]
#[requires(s.len() > 0)]
pub fn last_idx<T>(s: Seq<T>) -> Int {
    pearlite! { s.len()-1 }
}

#[logic]
#[cfg_attr(all(any(trust_all, trust_logic), all(not(untrust_all), not(untrust_all_logic))), trusted)]
#[requires(s.len() > 0)]
pub fn last_elem<T>(s: Seq<T>) -> T {
    pearlite! { s[s.len()-1] }
}

#[logic]
#[requires(s.len() > 0)]
#[requires(sorted(s))]
#[ensures(sorted(pop(s)))]
pub fn lemma_pop_maintains_sorted(s: Seq<usize>) {}