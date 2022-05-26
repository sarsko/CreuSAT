extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::logic::Ghost;
use creusot_contracts::*;

#[cfg(feature = "contracts")]
use crate::logic::logic_util::*;


// Selection sort with larger elements first. Based on the one in Creusot repo by me and Xavier
#[cfg_attr(feature = "trust_util", trusted)]
#[ensures(sorted_rev(@^v))]
#[ensures((@^v).permutation_of(@v))]
pub fn sort_reverse(v: &mut Vec<(usize, usize)>) {
    let mut i: usize = 0;
    let old_v = ghost! { v };
    #[invariant(proph_const, ^v == ^old_v.inner())]
    #[invariant(permutation, (@v).permutation_of(@*old_v.inner()))]
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

#[cfg_attr(feature = "trust_util", trusted)]
#[inline(always)]
pub fn update_fast(fast: &mut usize, lbd: usize) {
    *fast -= *fast / 32;
    let lbd_shl_fifteen = if lbd < usize::MAX / 32768 { lbd * 32768 } else { lbd };
    if usize::MAX - *fast > lbd_shl_fifteen {
        *fast += lbd_shl_fifteen;
    }
}

#[cfg_attr(feature = "trust_util", trusted)]
#[inline(always)]
pub fn update_slow(slow: &mut usize, lbd: usize) {
    *slow -= *slow / 32768;
    let lbd_shl_five = if lbd < usize::MAX / 32 { lbd * 32 } else { lbd };
    if usize::MAX - *slow > lbd_shl_five {
        *slow += lbd_shl_five;
    }
}
/*
#[cfg_attr(feature = "trust_util", trusted)]
#[ensures(sorted_tuple_first(@^v))]
#[ensures((@^v).permutation_of(@v))]
pub fn insertion_sort(arr: &mut Vec<(usize, usize)>) {
    let mut i = 1;
    while i < arr.len() {
        let mut j = i;
        while j > 0 && arr[j].0 < arr[j-1].0 {
            arr.swap(j, j-1);
            j = j-1;
        }
        i += 1;
    }
}
*/

// Regular selection sort. Based on the one in Creusot repo by me and Xavier
#[cfg_attr(feature = "trust_util", trusted)]
#[ensures(sorted_tuple_zeroth(@^v))]
#[ensures((@^v).permutation_of(@v))]
pub fn sort(v: &mut Vec<(usize, usize)>) {
    let mut i: usize = 0;
    let old_v = ghost! { v };
    #[invariant(proph_const, ^v == ^old_v.inner())]
    #[invariant(permutation, (@v).permutation_of(@*old_v.inner()))]
    #[invariant(i_bound, @i <= (@v).len())]
    #[invariant(sorted, sorted_range_tuple_zeroth(@v, 0, @i))]
    #[invariant(partition, partition(@v, @i))]
    while i < v.len() {
        let mut max = i;
        let mut j = i + 1;
        #[invariant(max_is_max, forall<k: Int> @i <= k && k < @j ==> (@v)[@max].0 <= (@v)[k].0)]
        #[invariant(j_bound, @i <= @j && @j <= (@v).len())]
        #[invariant(max_bound, @i <= @max && @max < @j)]
        while j < v.len() {
            if v[j].0 < v[max].0 {
                max = j;
            }
            j += 1;
        }
        v.swap(i, max);
        i += 1;
    }
}
