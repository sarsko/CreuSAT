extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

#[predicate]
fn sorted_range_rev(s: Seq<(usize, usize)>, l: Int, u: Int) -> bool {
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
fn partition_rev(v: Seq<(usize, usize)>, i: Int) -> bool {
    pearlite! { forall<k1 : Int, k2: Int> 0 <= k1 && k1 < i && i <= k2 && k2 < v.len() ==> v[k1].0 >= v[k2].0}
}

// Selection sort with larger elements first. Based on the one in Creusot repo by me and Xavier
#[ensures(sorted_rev(@^v))]
#[ensures((@^v).permutation_of(@v))]
pub fn sort_reverse(v: &mut Vec<(usize, usize)>) {
    let mut i: usize = 0;
    let old_v = Ghost::record(&v);
    #[invariant(proph_const, ^v == ^@old_v)]
    #[invariant(permutation, (@v).permutation_of(@*@old_v))]
    #[invariant(i_bound, @i <= (@v).len())]
    #[invariant(sorted, sorted_range_rev(@v, 0, @i))]
    #[invariant(partition, partition_rev(@v, @i))]
    while i < v.len() {
        let mut max = i;
        let mut j = i + 1;
        #[invariant(max_is_max, forall<k: Int> @i <= k && k < @j ==> (@v)[@max].0 >= (@v)[k].0)]
        #[invariant(j_bound, @i <= @j && @j <= (@v).len())]
        #[invariant(max_bound, @i <= @max && @max < @j)]
        while j < v.len() {
            if v[j].0 > v[max].0 {
                max = j;
            }
            j += 1;
        }
        v.swap(i, max);
        i += 1;
    }
}
