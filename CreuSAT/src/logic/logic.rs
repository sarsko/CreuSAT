extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{assignments::*, clause::*, formula::*, lit::*, trail::*};

use crate::logic::{logic_assignments::*, logic_clause::*, logic_formula::*, logic_trail::*};

#[logic]
fn pos() -> AssignedState {
    1u8
}

#[logic]
fn neg() -> AssignedState {
    0u8
}

#[predicate]
pub fn unset(v: AssignedState) -> bool {
    pearlite! {
        if @v >= 2 {
            true
        } else {
            false
        }
    }
}

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
#[requires(c.in_formula_inner(f))]
#[requires(c2.in_formula_inner(f))]
#[requires(c3.resolvent_of(c, c2, k, m))]
//#[ensures(equisat_compatible_inner(f, (f.0.push(c3), f.1)))]
#[ensures(equisat_extension_inner(c3, f))]
fn lemma_extended_formula_is_equisat_compatible(
    f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, k: Int, m: Int,
) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    //lemma_not_sat_gives_not_sat(f, c, c2, c3, k, m);
    //lemma_sat_gives_sat(f, c, c2, c3, k, m);
}

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
    // lemma_not_sat_gives_not_sat(f, c, c2, c3);
    // lemma_sat_gives_sat(f, c, c2, c3, k, m);
    lemma_extended_formula_is_equisat_compatible(f, c, c2, c3, k, m);
}

// CDCL STUFF END

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[ensures(b ==> @result == 1)]
#[ensures(!b ==> @result == 0)]
pub fn bool_to_assignedstate(b: bool) -> AssignedState {
    if b {
        1u8
    } else {
        0u8
    }
}

#[logic]
fn flip_v(v: AssignedState) -> AssignedState {
    pearlite! {
        if @v == 0 {
            1u8
        } else if @v == 1 {
            0u8
        } else {
            v
        }
    }
}