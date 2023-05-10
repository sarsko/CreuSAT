extern crate creusot_contracts;

use creusot_contracts::logic::FSet;
use creusot_contracts::*;

use crate::lit::*;

#[logic]
#[why3::attr = "inline:trivial"]
pub(crate) fn bool_as_u8(b: bool) -> u8 {
    pearlite! {
       match b {
           true => 1u8,
           false => 0u8,
       }
    }
}

#[logic]
#[why3::attr = "inline:trivial"]
pub(crate) fn bool_as_int(b: bool) -> Int {
    pearlite! {
       match b {
           true => 1,
           false => 0,
       }
    }
}

#[logic]
#[ensures(forall<i: Int> 0 <= i && i < seq.len() ==> result.contains(seq[i]))]
#[ensures(forall<l: _> result.contains(l) ==> exists<i: Int> 0 <= i && i < seq.len() && seq[i] == l)]
pub(crate) fn seq_to_fset(seq: Seq<LitModel>) -> FSet<LitModel> {
    pearlite! {
        seq_to_fset_internal(seq, 0)
    }
}

#[logic]
#[variant(seq.len() - idx)]
#[requires(idx >= 0)]
#[ensures(forall<l: _> result.contains(l) ==> exists<i: _> idx <= i && i < seq.len() && seq[i] == l)]
#[ensures(forall<i: Int> idx <= i && i < seq.len() ==> result.contains(seq[i]))]
fn seq_to_fset_internal(seq: Seq<LitModel>, idx: Int) -> FSet<LitModel> {
    pearlite! {
        if idx < seq.len() {
            let set = seq_to_fset_internal(seq, idx + 1);
            set.insert(seq[idx])
        } else {
            FSet::EMPTY
        }
    }
}
