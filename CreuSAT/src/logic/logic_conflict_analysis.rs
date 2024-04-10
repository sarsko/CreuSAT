extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::clause::*;
use crate::formula::Formula;
use crate::logic::{logic_assignments::*, logic_clause::*, logic_formula::*};

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[open] //#[open(self)]
#[requires(f2.clauses == f.clauses.push(c))]
#[requires(formula_invariant(f))]
#[ensures(f.clauses.len() + 1 == f2.clauses.len())]
#[ensures(forall<i: Int> 0 <= i && i < f.clauses.len() ==> f.clauses[i].equals(f2.clauses[i]))]
#[ensures(f2.clauses[f2.clauses.len()-1]@ == c@)]
//#[ensures(formula_invariant(f2))]
//#[ensures(f.num_vars == f2.num_vars)]
pub fn lemma_eq_formulas(f: FormulaModel, f2: FormulaModel, c: Clause) {}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[open] //#[open(self)]
#[requires(formula_invariant(f))]
#[requires(equisat_extension_inner(c, f))]
#[requires(c2.in_formula_inner(f))]
#[requires(c3.resolvent_of(c, c2, k, m))]
#[ensures(equisat_extension_inner(c3, f))]
pub fn lemma_resolvent_of_equisat_extension_is_equisat(
    f: FormulaModel, c: Clause, c2: Clause, c3: Clause, k: Int, m: Int,
) {
    lemma_eq_formulas(f, FormulaModel { clauses: f.clauses.push(c3), num_vars: f.num_vars }, c3);
}
