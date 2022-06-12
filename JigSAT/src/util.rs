pub fn sort_reverse(v: &mut Vec<(usize, usize)>) {
    let mut i: usize = 0;
    while i < v.len() {
        let mut max = i;
        let mut j = i + 1;
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

#[inline]
pub fn update_fast(fast: &mut usize, lbd: usize) {
    *fast -= *fast / 32;
    let lbd_shl_fifteen = if lbd < usize::MAX / 32768 { lbd * 32768 } else { lbd };
    if usize::MAX - *fast > lbd_shl_fifteen {
        *fast += lbd_shl_fifteen;
    }
}

#[inline]
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

pub fn sort(v: &mut Vec<(usize, usize)>) {
    let mut i: usize = 0;
    while i < v.len() {
        let mut max = i;
        let mut j = i + 1;
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
