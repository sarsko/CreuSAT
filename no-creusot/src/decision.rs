use crate::formula::*;
use crate::lit::*;

use ordered_float::OrderedFloat;
pub struct Decisions {
    pub lit_order: Vec<usize>,
}

impl Decisions {
    pub fn new(f: &Formula) -> Decisions {
        let mut lit_order = vec![0; f.num_vars];
        let mut counts = vec![0; f.num_vars];
        let mut i = 0;  
        while i < f.num_vars {
            let curr_clause = &f.clauses[i];
            counts[curr_clause.first.idx] += 1;
            counts[curr_clause.second.idx] += 1;
            let mut j = 0;
            while j < curr_clause.rest.len() {
                counts[curr_clause.rest[j].idx] += 1;
                j += 1;
            }
            i += 1;
        }
        let mut counts_with_index = vec![(0, 0); f.num_vars];
        i = 0;
        while i < f.num_vars {
            counts_with_index[i] = (counts[i], i);
            i += 1;
        }
        counts_with_index.sort_by_key(|k| -k.0);
        i = 0;
        while i < f.num_vars {
            lit_order[i] = counts_with_index[i].1;
            i += 1;
        }
        Decisions{lit_order: lit_order}
    }
}