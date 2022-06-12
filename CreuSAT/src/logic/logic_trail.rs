extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{assignments::*, clause::*, formula::*, lit::*, trail::*};

#[cfg(feature = "contracts")]
use crate::logic::{logic::*, logic_clause::*, logic_util::*};

impl Reason {
    #[predicate]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            match self {
                Reason::Long(cref) =>
                    (0 <= @cref && @cref < (@f.clauses).len())
                    && (@(@f.clauses)[@cref]).len() > 1,
                Reason::Unit(cref) =>
                    (0 <= @cref && @cref < (@f.clauses).len())
                    && (@(@f.clauses)[@cref]).len() == 1,
                _ => true
            }
        }
    }

    #[predicate]
    pub fn invariant_reason_new(self, f: Formula, a: Assignments) -> bool {
        pearlite! {
            match self {
                Reason::Long(cref) =>
                    (0 <= @cref && @cref < (@f.clauses).len())
                    && (@(@f.clauses)[@cref]).len() > 1
                    && (forall<i: Int> 1 <= i && i < (@(@f.clauses)[@cref]).len() ==>
                        (@(@f.clauses)[@cref])[i].unsat_inner(@a))
                    && (@(@f.clauses)[@cref])[0].sat_inner(@a),
                Reason::Unit(cref) =>
                    (0 <= @cref && @cref < (@f.clauses).len())
                    && (@(@f.clauses)[@cref]).len() == 1
                    && (@(@f.clauses)[@cref])[0].sat_inner(@a),
                _ => true
            }
        }
    }
}

impl Step {
    #[predicate]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            self.lit.invariant(@f.num_vars) &&
            self.reason.invariant(f)
        }
    }
}

// LOGIC
impl Trail {
    #[predicate]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            self.invariant_no_decision(f) &&
            (forall<i: Int> 0 <= i && i < (@self.decisions).len() ==> @(@self.decisions)[i] <= (@self.trail).len())
        }
    }

    #[predicate]
    fn invariant_no_decision_mirror(self, f: Formula) -> bool {
        pearlite! {
            (@f.num_vars == (@self.assignments).len() && forall<i : Int> 0 <= i && i < (@self.assignments).len() ==> @(@self.assignments)[i] <= 3)
            && (forall<i: Int> 0 <= i && i < (@self.trail).len() ==> (@self.trail)[i].invariant(f))
            && (@self.lit_to_level).len() == @f.num_vars
            && (forall<i: Int> 0 <= i && i < (@self.trail).len() ==>
                    forall<j: Int> 0 <= j && j < i ==>
                        match (@self.trail)[j].reason {
                            Reason::Long(cref) => !(@self.trail)[i].lit.lit_idx_in((@f.clauses)[@cref]),
                            _ => true,
                        }) // lit_not_in_less_inner(@self.trail, f)
            && lit_is_unique_inner(@self.trail)
            && long_are_post_unit_inner(@self.trail, f, @self.assignments)
            && (forall<j: Int> 0 <= j && j < (@self.trail).len() ==> (@self.trail)[j].lit.sat(self.assignments))
            && sorted(@self.decisions)
            && unit_are_sat(@self.trail, f, self.assignments)
        }
    }

    #[predicate]
    #[ensures(result == self.invariant_no_decision_mirror(f))]
    pub fn invariant_no_decision(self, f: Formula) -> bool {
        pearlite! {
            self.assignments.invariant(f)
            && trail_invariant(@self.trail, f)
            && lit_to_level_invariant(@self.lit_to_level, f)
            // added, watch out
            && self.lit_not_in_less(f)
            && self.lit_is_unique()
            && long_are_post_unit_inner(@self.trail, f, @self.assignments)
            && self.trail_entries_are_assigned()
            && self.decisions_are_sorted()
            && unit_are_sat(@self.trail, f, self.assignments)
            // assignments_are_in_trail(@self.trail, @self.assignments) // Gonna get added in the future
        }
    }

    #[predicate]
    pub fn new_post_unit(self, f: Formula) -> bool {
        pearlite! {
            forall<j: Int> 0 <= j && j < (@self.trail).len() ==>
            (@self.trail)[j].reason.invariant_reason_new(f, self.assignments)
        }
    }

    #[predicate]
    pub fn trail_entries_are_assigned(self) -> bool {
        pearlite! {
            trail_entries_are_assigned_inner(@self.trail, @self.assignments)
        }
    }

    #[predicate]
    pub fn decisions_are_sorted(self) -> bool {
        pearlite! {
            sorted(@self.decisions)
        }
    }

    #[predicate]
    pub fn lit_not_in_less(self, f: Formula) -> bool {
        pearlite! {
            // moved into function. May break stuff
            lit_not_in_less_inner(@self.trail, f)
        }
    }

    // Trail does not contail duplicate idxes
    #[predicate]
    pub fn lit_is_unique(self) -> bool {
        pearlite! {
            lit_is_unique_inner(@self.trail)
        }
    }
}

#[predicate]
pub fn lit_not_in_less_inner(t: Seq<Step>, f: Formula) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < t.len() ==>
            forall<j: Int> 0 <= j && j < i ==>
                match t[j].reason {
                    Reason::Long(cref) => !(t)[i].lit.lit_idx_in((@f.clauses)[@cref]),
                    _ => true,
                }
    }
}

#[predicate]
pub fn trail_invariant(trail: Seq<Step>, f: Formula) -> bool {
    pearlite! {
        crefs_in_range(trail, f)
    }
}

#[predicate]
fn lit_to_level_invariant(lit_to_level: Seq<usize>, f: Formula) -> bool {
    pearlite! {
        lit_to_level.len() == @f.num_vars
    }
}

#[predicate]
//#[ensures(result == (forall<i: Int> 0 <= i && i < trail.len() ==> trail[i].invariant(f)))]
pub fn crefs_in_range(trail: Seq<Step>, f: Formula) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < trail.len() ==>
            trail[i].invariant(f)
    }
}

#[predicate]
fn trail_entries_are_assigned_inner(t: Seq<Step>, a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < t.len() ==>
            t[j].lit.sat_inner(a) // Should be equivalent
    }
}

#[predicate]
pub fn clause_post_with_regards_to(c: Clause, a: Assignments, j: Int) -> bool {
    pearlite! {
        clause_post_with_regards_to_inner(c, @a, j)
    }
}

#[predicate]
pub fn clause_post_with_regards_to_inner(c: Clause, a: Seq<AssignedState>, j: Int) -> bool {
    pearlite! {
        (@c)[0].index_logic() == j
        && (@c)[0].sat_inner(a)
        && (forall<i: Int> 1 <= i && i < (@c).len() ==> (@c)[i].unsat_inner(a))
    }
}

#[predicate]
pub fn clause_post_with_regards_to_lit(c: Clause, a: Assignments, lit: Lit) -> bool {
    pearlite! {
        clause_post_with_regards_to_inner(c, @a, @lit.idx)
    }
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
        forall<j: Int> 0 <= j && j < (@trail.trail).len() ==>
        match (@trail.trail)[j].reason {
            Reason::Long(k) => { clause_post_with_regards_to((@f.clauses)[@k], trail.assignments, (@trail.trail)[j].lit.index_logic()) },
                _ => true,
            }
    }
}

#[predicate]
pub fn long_are_post_unit_inner(trail: Seq<Step>, f: Formula, a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < trail.len() ==>
            match trail[j].reason {
                Reason::Long(k) => { clause_post_with_regards_to_inner((@f.clauses)[@k], a, (trail)[j].lit.index_logic()) },
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
                    trail[j].lit == (@(@f.clauses)[@k])[0]
                    && (@(@f.clauses)[@k])[0].sat(a) },
                    _ => true,
                }
    }
}

#[cfg_attr(feature = "trust_trail_logic", trusted)]
#[logic]
#[requires(a.invariant(f))]
#[requires(f.invariant())]
#[requires(trail_invariant(v, f))]
#[requires(crefs_in_range(v, f))]
#[requires(lit.invariant(@f.num_vars))]
#[requires(unset((@a)[lit.index_logic()]))]
#[requires(long_are_post_unit_inner(v, f, @a))]
#[ensures(long_are_post_unit_inner(v, f, (@a).set(lit.index_logic(), 1u8)))]
#[ensures(long_are_post_unit_inner(v, f, (@a).set(lit.index_logic(), 0u8)))]
pub fn lemma_assign_maintains_long_are_post_unit(v: Seq<Step>, f: Formula, a: Assignments, lit: Lit) {}

#[cfg_attr(feature = "trust_trail_logic", trusted)]
#[logic]
#[requires(f.invariant())]
#[requires(t.invariant(f))]
#[requires(unset((@t.assignments)[step.lit.index_logic()]))]
#[requires(step.invariant(f))]
#[requires(lit_not_in_less_inner(@t.trail, f))]
#[ensures(lit_not_in_less_inner((@t.trail).push(step), f))]
pub fn lemma_push_maintains_lit_not_in_less(t: Trail, f: Formula, step: Step) {}
