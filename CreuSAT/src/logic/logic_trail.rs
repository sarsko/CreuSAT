extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{assignments::*, clause::*, formula::*, lit::*, trail::*};

#[cfg(creusot)]
use crate::logic::{logic::*, logic_clause::*, logic_util::*};

impl Reason {
    #[predicate]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            match self {
                Reason::Long(cref) =>
                    (0 <= cref@ && cref@ < f.clauses@.len())
                    && f.clauses@[cref@]@.len() > 1,
                Reason::Unit(cref) =>
                    (0 <= cref@ && cref@ < f.clauses@.len())
                    && f.clauses@[cref@]@.len() == 1,
                _ => true
            }
        }
    }

    /*
    #[predicate]
    pub fn invariant_reason_new(self, f: Formula, a: Assignments) -> bool {
        pearlite! {
            match self {
                Reason::Long(cref) =>
                    (0 <= cref@ && cref@ < f.clauses@.len())
                    && (@f.clauses@[cref@]).len() > 1
                    && (forall<i: Int> 1 <= i && i < (@f.clauses@[cref@]).len() ==>
                        (@f.clauses@[cref@])[i].unsat_inner(a@))
                    && (@f.clauses@[cref@])[0].sat_inner(a@),
                Reason::Unit(cref) =>
                    (0 <= cref@ && cref@ < f.clauses@.len())
                    && (@f.clauses@[cref@]).len() == 1
                    && (@f.clauses@[cref@])[0].sat_inner(a@),
                _ => true
            }
        }
    }
    */
}

// LOGIC
impl Trail {
    #[predicate]
    #[why3::attr = "inline:trivial"]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            self.assignments.invariant(f)
            && trail_invariant(self.trail@, f)
            && self.lit_to_level@.len() == f.num_vars@
            && lit_not_in_less_inner(self.trail@, f)
            && lit_is_unique_inner(self.trail@)
            && long_are_post_unit_inner(self.trail@, f, self.assignments@)
            && trail_entries_are_assigned_inner(self.trail@, self.assignments@)
            && sorted(self.decisions@)
            && unit_are_sat(self.trail@, f, self.assignments)
            && (forall<i: Int> 0 <= i && i < self.decisions@.len() ==> self.decisions@[i]@ <= self.trail@.len())
        }
    }

    #[predicate]
    #[why3::attr = "inline:trivial"]
    pub fn invariant_no_decision(self, f: Formula) -> bool {
        pearlite! {
            self.assignments.invariant(f)
            && trail_invariant(self.trail@, f)
            && self.lit_to_level@.len() == f.num_vars@
            && lit_not_in_less_inner(self.trail@, f)
            && lit_is_unique_inner(self.trail@)
            && long_are_post_unit_inner(self.trail@, f, self.assignments@)
            && trail_entries_are_assigned_inner(self.trail@, self.assignments@)
            && sorted(self.decisions@)
            && unit_are_sat(self.trail@, f, self.assignments)
        }
    }
}

#[predicate]
pub fn lit_not_in_less_inner(t: Seq<Step>, f: Formula) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < t.len() ==>
            forall<j: Int> 0 <= j && j < i ==>
                match t[j].reason {
                    Reason::Long(cref) => !(t)[i].lit.lit_idx_in(f.clauses@[cref@]),
                    _ => true,
                }
    }
}

#[predicate]
pub fn trail_invariant(trail: Seq<Step>, f: Formula) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < trail.len() ==>
              (trail[i].lit.invariant(f.num_vars@)
            && trail[i].reason.invariant(f))
    }
}

#[predicate]
fn trail_entries_are_assigned_inner(t: Seq<Step>, a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < t.len() ==>
            t[j].lit.sat_inner(a)
    }
}

#[predicate]
pub fn clause_post_with_regards_to(c: Clause, a: Assignments, j: Int) -> bool {
    pearlite! { clause_post_with_regards_to_inner(c, a@, j) }
}

#[predicate]
pub fn clause_post_with_regards_to_inner(c: Clause, a: Seq<AssignedState>, j: Int) -> bool {
    pearlite! {
        c@[0].index_logic() == j
        && c@[0].sat_inner(a)
        && (forall<i: Int> 1 <= i && i < c@.len() ==> c@[i].unsat_inner(a))
    }
}

#[predicate]
pub fn clause_post_with_regards_to_lit(c: Clause, a: Assignments, lit: Lit) -> bool {
    pearlite! { clause_post_with_regards_to_inner(c, a@, lit.idx@) }
}

#[predicate]
fn lit_is_unique_inner(trail: Seq<Step>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < trail.len() ==>
            forall<j: Int> 0 <= j && j < i ==>
                trail[j].lit.index_logic() != trail[i].lit.index_logic()
    }
}

#[predicate]
pub fn long_are_post_unit(trail: Trail, f: Formula) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < trail.trail@.len() ==>
        match trail.trail@[j].reason {
            Reason::Long(k) => { clause_post_with_regards_to(f.clauses@[k@], trail.assignments, trail.trail@[j].lit.index_logic()) },
                _ => true,
            }
    }
}

#[predicate]
pub fn long_are_post_unit_inner(trail: Seq<Step>, f: Formula, a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < trail.len() ==>
            match trail[j].reason {
                Reason::Long(k) => { clause_post_with_regards_to_inner(f.clauses@[k@], a, trail[j].lit.index_logic()) },
                    _ => true,
                }
    }
}

#[predicate]
fn unit_are_sat(trail: Seq<Step>, f: Formula, a: Assignments) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < trail.len() ==>
            match trail[j].reason {
                Reason::Unit(k) => {
                    trail[j].lit == f.clauses@[k@]@[0]
                    && f.clauses@[k@]@[0].sat(a) },
                    _ => true,
                }
    }
}

/*
#[cfg_attr(feature = "trust_trail_logic", trusted)]
#[logic]
#[requires(a.invariant(f))]
#[requires(f.invariant())]
#[requires(trail_invariant(v, f))]
#[requires(crefs_in_range(v, f))]
#[requires(lit.invariant(f.num_vars@))]
#[requires(unset((a@)[lit.index_logic()]))]
#[requires(long_are_post_unit_inner(v, f, a@))]
#[ensures(long_are_post_unit_inner(v, f, (a@).set(lit.index_logic(), 1u8)))]
#[ensures(long_are_post_unit_inner(v, f, (a@).set(lit.index_logic(), 0u8)))]
pub fn lemma_assign_maintains_long_are_post_unit(v: Seq<Step>, f: Formula, a: Assignments, lit: Lit) {}
*/

#[cfg_attr(feature = "trust_trail_logic", trusted)]
#[logic]
#[requires(f.invariant())]
#[requires(t.invariant(f))]
#[requires(unset(t.assignments@[step.lit.index_logic()]))]
#[requires(step.lit.invariant(f.num_vars@))]
//#[requires(step.reason.invariant(f))]
#[requires(lit_not_in_less_inner(t.trail@, f))]
#[ensures(lit_not_in_less_inner(t.trail@.push(step), f))]
pub fn lemma_push_maintains_lit_not_in_less(t: Trail, f: Formula, step: Step) {}
