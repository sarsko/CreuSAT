extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{assignments::*, clause::*, conflict_analysis::*, formula::*, lit::*, trail::*};

#[cfg(feature = "contracts")]
use crate::logic::{logic::*, logic_clause::*};

#[cfg_attr(feature = "trust_conflict_logic", trusted)]
#[logic]
//#[requires(@v[i].idx === idx)]
#[requires(0 <= c_idx && c_idx < c.len() && @(c)[c_idx].idx === idx &&
    (exists<k: Int> 0 <= k && k < o.len() && k != i &&
        o[k].is_opp(c[c_idx]))
)]
#[requires(forall<j: Int, k: Int> 0 <= j && j < o.len() && 0 <= k && k < c.len() &&
    k != c_idx && @o[j].idx != idx ==> !c[k].is_opp((o)[j]))]
#[requires(0 <= i && i < o.len() && @o[i].idx != idx)]
#[requires(invariant_internal(o, @_f.num_vars))]
#[requires(invariant_internal(c, @_f.num_vars))]
#[requires(forall<j: Int> 0 <= j && j < c.len() && @c[j].idx != idx ==> c[j].lit_in_internal(new))]
#[requires(forall<j: Int> 0 <= j && j < new.len() ==> (new)[j].lit_in_internal(c) || (new)[j].lit_in_internal(o))]
#[requires(exists<k: Int> 0 <= k && k < new.len() && @o[i].idx === @(new)[k].idx)]
#[ensures(exists<k: Int> 0 <= k && k < c.len() && @o[i].idx === @c[k].idx || (o)[i].lit_in_internal(new))]
#[ensures(exists<k: Int> 0 <= k && k < c.len() && @o[i].idx === @c[k].idx && o[i].polarity === c[k].polarity || (o)[i].lit_in_internal(new))]
//#[ensures(((o)[i].lit_in_internal(new)))]
pub fn lemma_idx(
    c: Seq<Lit>,
    o: Seq<Lit>,
    new: Seq<Lit>,
    i: Int,
    idx: Int,
    c_idx: Int,
    _f: Formula,
) {
}

// OK [04.04] [[Doesnt check out on Mac [04.04]. Super easy on Linux]]
#[cfg_attr(feature = "trust_conflict_logic", trusted)]
#[logic]
//#[requires(@v[i].idx === idx)]
#[requires(0 <= c_idx && c_idx < c.len() && @(c)[c_idx].idx === idx &&
    (exists<k: Int> 0 <= k && k < o.len() && k != i &&
        o[k].is_opp(c[c_idx]))
)]
#[requires(forall<j: Int, k: Int> 0 <= j && j < o.len() && 0 <= k && k < c.len() &&
    k != c_idx && @o[j].idx != idx ==> !c[k].is_opp((o)[j]))]
#[requires(0 <= i && i < o.len() && @o[i].idx != idx)]
#[requires(invariant_internal(o, @_f.num_vars))]
#[requires(invariant_internal(c, @_f.num_vars))]
#[requires(forall<j: Int> 0 <= j && j < c.len() && @c[j].idx != idx ==> c[j].lit_in_internal(new))]
#[requires(forall<j: Int> 0 <= j && j < new.len() ==> (new)[j].lit_in_internal(c) || (new)[j].lit_in_internal(o))]
#[requires(exists<k: Int> 0 <= k && k < new.len() && @o[i].idx === @(new)[k].idx)]
#[ensures(((o)[i].lit_in_internal(new)))]
pub fn lemma_idx2(
    c: Seq<Lit>,
    o: Seq<Lit>,
    new: Seq<Lit>,
    i: Int,
    idx: Int,
    c_idx: Int,
    _f: Formula,
) {
    lemma_idx(c, o, new, i, idx, c_idx, _f);
}

/*
#[logic]
#[requires(c.invariant(a.len()))]
#[requires(c2.invariant(a.len()))]
#[requires(0 <= c_idx && c_idx < (@c).len())]
#[requires(0 <= c2_idx && c2_idx < (@c2).len())]
#[requires(c3.resolvent_of(c, c2, c2_idx, c_idx))]
//#[ensures((@c3).len() >= (@c2).len() - 1)]
#[ensures((forall<i: Int> 0 <= i && i < (@c ).len() && i != c_idx ==> (@c   )[i].lit_in(c3)))]
pub fn lemma_resolved_len(c: Clause, c2: Clause, c3: Clause, a: Seq<AssignedState>, c_idx: Int, c2_idx: Int) {}
*/

/*
#[requires(c.invariant(a.len()))]
#[requires(c2.invariant(a.len()))]
#[requires(0 <= c_idx && c_idx < (@c).len())]
#[requires((forall<i: Int> 0 <= i && i < (@c ).len() && i != c_idx ==> (@c   )[i].lit_in(c3)))]
#[ensures((@c3).len() + 1 >= (@c).len())]
pub fn lemma_resolved_len2(c: Clause, c2: Clause, c3: Clause, a: Seq<AssignedState>, c_idx: Int, c2_idx: Int) {}
*/
