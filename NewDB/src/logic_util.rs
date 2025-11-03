use creusot_contracts::logic::FSet;
use creusot_contracts::prelude::*;

use crate::lit::*;

#[logic(open, inline)]
pub fn bool_as_u8(b: bool) -> u8 {
    pearlite! {
       match b {
           true => 1u8,
           false => 0u8,
       }
    }
}

#[logic(open(crate))]
#[ensures(forall<i: Int> 0 <= i && i < seq.len() ==> result.contains(seq[i]))]
#[ensures(forall<l: _> result.contains(l) ==> exists<i: Int> 0 <= i && i < seq.len() && seq[i] == l)]
pub(crate) fn seq_to_fset(seq: Seq<Lit>) -> FSet<Lit> {
    pearlite! {
        seq_to_fset_internal(seq, 0)
    }
}

#[logic(open(crate))]
#[variant(seq.len() - idx)]
#[requires(idx >= 0)]
#[ensures(forall<l : _> result.contains(l) ==> exists<i : _> idx <= i && i < seq.len() && seq[i] == l)]
#[ensures(forall<i : Int> idx <= i && i < seq.len() ==> result.contains(seq[i]))]
pub(crate) fn seq_to_fset_internal(seq: Seq<Lit>, idx: Int) -> FSet<Lit> {
    pearlite! {
        if idx < seq.len() {
            let set = seq_to_fset_internal(seq, idx + 1);
            set.insert(seq[idx])
        } else {
            FSet::empty()
        }
    }
}
