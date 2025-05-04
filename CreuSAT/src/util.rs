
use creusot_contracts::{std::*, Snapshot, *};

#[cfg(creusot)]
use crate::logic::logic_util::*;

// Selection sort with larger elements first. Based on the one in Creusot repo by Xavier and I
#[cfg_attr(feature = "trust_util", trusted)]
#[ensures(sorted_rev((^v)@))]
#[ensures((^v)@.permutation_of(v@))]
pub fn sort_reverse(v: &mut Vec<(usize, usize)>) {
    let mut i: usize = 0;
    let old_v: Snapshot<&mut Vec<(usize, usize)>> = snapshot! { v };
    #[invariant(v@.permutation_of(old_v@))]
    #[invariant(i@ <= v@.len())]
    #[invariant(sorted_range_rev(v@, 0, i@))]
    #[invariant(partition_rev(v@, i@))]
    while i < v.len() {
        let mut max = i;
        let mut j = i + 1;
        #[invariant(forall<k: Int> i@ <= k && k < j@ ==> v@[max@].0 >= v@[k].0)]
        #[invariant(i@ <= j@ && j@ <= v@.len())]
        #[invariant(i@ <= max@ && max@ < j@)]
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

// Regular selection sort. Based on the one in Creusot repo by Xavier and I
#[cfg_attr(feature = "trust_util", trusted)]
#[ensures(sorted_tuple_zeroth((^v)@))]
#[ensures((^v)@.permutation_of(v@))]
pub fn sort(v: &mut Vec<(usize, usize)>) {
    let mut i: usize = 0;
    let old_v: Snapshot<&mut Vec<(usize, usize)>> = snapshot! { v };
    #[invariant(v@.permutation_of(old_v@))]
    #[invariant(i@ <= v@.len())]
    #[invariant(sorted_range_tuple_zeroth(v@, 0, i@))]
    #[invariant(partition(v@, i@))]
    while i < v.len() {
        let mut max = i;
        let mut j = i + 1;
        #[invariant(forall<k: Int> i@ <= k && k < j@ ==> v@[max@].0 <= v@[k].0)]
        #[invariant(i@ <= j@ && j@ <= v@.len())]
        #[invariant(i@ <= max@ && max@ < j@)]
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

#[logic]
#[open]
pub fn min_log(a: Int, b: Int) -> Int {
    if a <= b {
        a
    } else {
        b
    }
}

#[cfg_attr(feature = "trust_util", trusted)]
#[ensures(result@ == min_log(a@, b@))]
#[ensures(a@ <= b@ ==> result@ == a@)]
#[ensures(b@ < a@ ==> result@ == b@)]
#[ensures(result@ <= b@ && result@ <= a@)]
pub fn min(a: usize, b: usize) -> usize {
    if a <= b {
        a
    } else {
        b
    }
}

#[logic]
#[open]
pub fn max_log(a: Int, b: Int) -> Int {
    if a >= b {
        a
    } else {
        b
    }
}

#[cfg_attr(feature = "trust_util", trusted)]
#[ensures(result@ == max_log(a@, b@))]
pub fn max(a: usize, b: usize) -> usize {
    if a >= b {
        a
    } else {
        b
    }
}
