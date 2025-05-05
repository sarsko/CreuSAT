use creusot_contracts::std::*;
use creusot_contracts::{Clone, *};

#[cfg(creusot)]
use crate::logic::*;

use crate::{assignments::*, clause::*, formula::*, lit::*};

//#[cfg_attr(feature = "trust_trail_logic", trusted)]
/*
#[open]
#[logic]
#[requires(f.inv())]
#[requires(t.inv(f))]
#[requires(unset((@t.assignments)[step.lit.index_logic()]))]
#[requires(step.lit.inv(f.num_vars@))]
//#[requires(step.reason.inv(f))]
#[requires(lit_not_in_less_inner(@t.trail, f))]
#[ensures(lit_not_in_less_inner((@t.trail).push(step), f))]
pub fn lemma_push_maintains_lit_not_in_less(t: Trail, f: Formula, step: Step) {}
*/

#[open]
#[logic]
#[requires(c.sat(a))]
#[ensures(forall<c2: Clause> c2@.permutation_of(c@) ==> c2.sat(a))]
pub fn lemma_clause_permuted_maintains_sat(c: Clause, a: Assignments) {}

#[open]
#[logic]
#[requires(c.unsat(a))]
#[ensures(forall<c2: Clause> c2@.permutation_of(c@) ==> c2.unsat(a))]
pub fn lemma_clause_permuted_maintains_unsat(c: Clause, a: Assignments) {}

#[maintains((mut f).inv())]
#[requires(f.clauses@[cref@]@.len() >= 2)]
#[requires(cref@ < f.clauses@.len())]
#[requires(f.clauses@[cref@]@.len() > j@)]
#[requires(f.clauses@[cref@]@.len() > k@)]
#[requires(!f.clauses@[cref@]@[0].sat_inner(assignments@))]
#[ensures(((^f).clauses@[cref@]@.exchange(f.clauses@[cref@]@, j@, k@)))]
#[ensures(f.num_vars@ == (^f).num_vars@)]
#[ensures(f.clauses@.len() == (^f).clauses@.len())]
#[ensures(f.equisat(^f))] // This one is hard (both ways equisat)
fn swap(f: &mut Formula, cref: usize, j: usize, k: usize, assignments: Assignments) {
    let old_f: Snapshot<&mut Formula> = snapshot! { f };

    f.clauses[cref].lits.swap(j, k);

    proof_assert!(^f == ^old_f.inner());
}
