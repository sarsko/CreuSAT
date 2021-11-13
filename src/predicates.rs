extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;
use crate::ghost;
use crate::lit::*;
use crate::clause::*;
use crate::logic::*;
use crate::assignments::*;
use crate::formula::*;


#[predicate]
pub fn eventually_unsat_formula_inner(a: Seq<AssignedState>, f: Formula) -> bool {
    pearlite! {
        forall<a2: Seq<AssignedState>> compatible_complete_inner(a, a2) ==> not_sat_formula_inner(a2, f)
    }
}

#[predicate]
pub fn eventually_sat_formula_inner(a: Seq<AssignedState>, f: Formula) -> bool {
    pearlite! {
        exists<a2 : Assignments> compatible_inner(a, @a2) && f.sat(a2)
    }
}


#[predicate]
pub fn not_sat_formula_inner(a: Seq<AssignedState>, f: Formula) -> bool {
    pearlite! {
        exists<i: Int> 0 <= i && i < (@(f.clauses)).len() &&
        not_sat_clause_inner(a, (@(f.clauses))[i])
    }
}
#[predicate]
pub fn assignments_equality(a: Assignments, a2: Assignments) -> bool {
    pearlite! {
        (@a).len() === (@a2).len() &&
        forall<i: Int> 0 <= i && i < (@a).len() ==> (@a)[i] === (@a2)[i]
    }
}

#[predicate]
pub fn vars_in_range(n: Int, c: Clause) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < (@c).len() ==>
            (0 <= @((@c)[i]).idx && @((@c)[i]).idx < n)
    }
}

#[predicate]
pub fn compatible_inner(a: Seq<AssignedState>, a2: Seq<AssignedState>) -> bool {
    pearlite! {
        a.len() === a2.len() &&
        forall<i: Int> 0 <= i && i < a.len() ==>
        (a[i] === AssignedState::Unset) || a[i] === a2[i]
    }
}

#[predicate]
pub fn complete_inner(a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < a.len() ==> !(a[i] === AssignedState::Unset)
    }
}

#[predicate]
pub fn compatible_complete_inner(a: Seq<AssignedState>, a2: Seq<AssignedState>) -> bool {
    pearlite! {
        compatible_inner(a, a2) && complete_inner(a2)
    }
}
#[predicate]
pub fn sat_clause_inner(a: Seq<AssignedState>, c: Clause) -> bool {
    pearlite! {
        exists<i: Int> 0 <= i && i < (@c).len() ==>
            match a[@(@c)[i].idx] {
                AssignedState::Positive => (@c)[i].polarity,
                AssignedState::Negative => !(@c)[i].polarity,
                AssignedState::Unset => false,
            }
    }
}

#[predicate]
pub fn not_sat_clause_inner(a: Seq<AssignedState>, c: Clause) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < (@c).len() ==>
            match a[@(@c)[i].idx] {
                AssignedState::Positive => !(@c)[i].polarity,
                AssignedState::Negative => (@c)[i].polarity,
                AssignedState::Unset => false,
            }
    }
}
