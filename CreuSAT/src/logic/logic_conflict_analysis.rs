extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::clause::*;
use crate::logic::{logic_assignments::*, logic_clause::*, logic_formula::*};

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
//#[ensures(formula_invariant(f2))]
//#[ensures(f.1 == f2.1)]
#[requires(f2.0 == f.0.push(c))]
#[requires(formula_invariant(f))]
#[ensures((f.0).len() + 1 == (f2.0).len())]
#[ensures(forall<i: Int> 0 <= i && i < (f.0).len() ==> ((f.0)[i]).equals((f2.0)[i]))]
#[ensures(@(f2.0)[(f2.0).len()-1] == @c)]
fn lemma_eq_formulas(f: (Seq<Clause>, Int), f2: (Seq<Clause>, Int), c: Clause) {}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[requires(formula_invariant(f))]
#[requires(equisat_extension_inner(c, f))]
#[requires(c2.in_formula_inner(f))]
#[requires(c3.resolvent_of(c, c2, k, m))]
#[ensures(equisat_extension_inner(c3, f))]
pub fn lemma_resolvent_of_equisat_extension_is_equisat(
    f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, k: Int, m: Int,
) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
}
