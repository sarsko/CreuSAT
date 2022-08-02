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
