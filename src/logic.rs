extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;
use crate::ghost;
use crate::lit::*;
use crate::clause::*;
use crate::predicates::*;
use crate::assignments::*;
use crate::formula::*;

#[logic]
#[variant(a.len())]
pub fn unassigned_count(a: Seq<AssignedState>) -> Int {
    if a.len() == 0 {
        0
    } else if pearlite! { a[0] === AssignedState::Unset } {
        1 + unassigned_count(a.tail())
    } else {
        unassigned_count(a.tail())
    }
}

#[logic]
#[variant(c.len())]
pub fn unassigned_count_clause_partial(c: Seq<Lit>, a: Seq<AssignedState>, i: Int) -> Int {
    if c.len() == 0  || i == 0 {
        0
    } else if pearlite! { a[@c[0].idx] === AssignedState::Unset } {
            1 + unassigned_count_clause_partial(c.tail(), a, i - 1)
    } else {
            unassigned_count_clause_partial(c.tail(), a, i - 1)
    }
}

#[logic]
#[variant(c.len())]
pub fn unassigned_count_clause(c: Seq<Lit>, a: Seq<AssignedState>) -> Int {
    if c.len() == 0 {
        0
    } else if pearlite! { a[@c[0].idx] === AssignedState::Unset } {
            1 + unassigned_count_clause(c.tail(), a)
    } else {
            unassigned_count_clause(c.tail(), a)
    }
}

#[logic]
#[ensures(b ==> result === AssignedState::Positive)]
#[ensures(!b ==> result === AssignedState::Negative)]
pub fn bool_to_assignedstate(b: bool) -> AssignedState {
    if b {
        AssignedState::Positive
    } else {
        AssignedState::Negative
    }
}

// Negation causes a syntax error otherwise
#[logic]
#[ensures(!b ==> result === AssignedState::Positive)]
#[ensures(b ==> result === AssignedState::Negative)]
pub fn bool_to_assignedstate_negated(b: bool) -> AssignedState {
    if !b {
        AssignedState::Positive
    } else {
        AssignedState::Negative
    }
}

#[logic]
#[trusted]
#[requires(c.unit(a))]
#[requires(0 <= i && i < (@c).len())]
#[variant((@c).len() - i)]
pub fn unit_get_literal_internal(c: Clause, a: Assignments, i: Int) -> Lit {
    pearlite! {
        if (@a.0)[@(@c.0)[i].idx] === AssignedState::Unset {
            (@c.0)[i]
        } else {
            unit_get_literal_internal(c, a, i + 1)
        }
    }
}

#[logic]
#[requires(c.unit(a))]
pub fn unit_get_literal(c: Clause, a: Assignments) -> Lit {
    unit_get_literal_internal(c, a, 0)
}




#[logic]
pub fn has_to_assign2(c: Clause, a: Assignments) -> bool{
    pearlite! {
        c.unit(a) ==> not_sat_clause_inner((@a).set(@unit_get_literal(c, a).idx, bool_to_assignedstate_negated(unit_get_literal(c, a).polarity)), c)
    }
}

#[logic]
#[trusted]
#[requires(0 <= i && i < (@c).len())]
#[variant((@c).len() - i)]
pub fn unit_get_literal_internal2(c: Clause, a: Seq<AssignedState>, i: Int) -> Lit {
    pearlite! {
        if (a)[@(@c.0)[i].idx] === AssignedState::Unset {
            (@c.0)[i]
        } else {
            unit_get_literal_internal2(c, a, i + 1)
        }
    }
}

#[logic]
pub fn unit_get_literal2(c: Clause, a: Seq<AssignedState>) -> Lit {
    unit_get_literal_internal2(c, a, 0)
}


/*
#[logic]
pub fn lemma_assign_unit(c: Clause, f: Formula, a: Assignments) -> bool{
    pearlite! {
        eventually_unsat_formula_inner(@a, f) && c.unit(a) ==>
          (forall<i: Int> 0 <= i && i < (@c).len() && (@a)[@(@c)[i].idx] === AssignedState::Unset &&
            eventually_unsat_formula_inner((@a).set(@(@c)[i].idx, AssignedState::Positive), f) &&
            eventually_unsat_formula_inner((@a).set(@(@c)[i].idx, AssignedState::Negative), f)
        )
    }
}
*/
// Add a lemma to show that a unit clause is equivalent to a clause with less clauses

/*
#[logic]
pub fn lemma_two() -> bool {
    pearlite! { true ==> true }
}
*/

/*
// Implication with ensures/requries breaks TODO tell Xavier
#[logic]
#[requires(c.unit(a))]
#[requires(0 <= (@l.idx) && (@l.idx) < (@a).len())]  
#[requires(l.lit_in(c))]
#[requires((@a)[@l.idx] === AssignedState::Unset)]
#[requires(l.polarity)]
#[requires(eventually_sat_formula_inner(@a, f))]
#[ensures(eventually_sat_formula_inner((@a).set(@l.idx, AssignedState::Positive), f))]
pub fn lemma_two(a: Assignments, f: Formula, l: Lit, c: Clause) -> bool{
    pearlite! { true ==> true }
}
*/

    /*
#[logic]
#[requires(c.unit(a))]
#[requires(0 <= (@l.idx) && (@l.idx) < (@a).len())]  
#[requires(l.lit_in(c))]
#[requires((@a)[@l.idx] === AssignedState::Unset)]
#[requires(l.polarity)]
#[requires(eventually_sat_formula_inner(@a, f))]
#[ensures(c.sat(a))]
#[ensures(eventually_sat_formula_inner((@a).set(@l.idx, AssignedState::Positive), f))]
pub fn lemma_pos(a: Assignments, f: Formula, l: Lit, c: Clause) -> bool{
    pearlite! {
        eventually_sat_formula_inner(@a, f)//&& c.unit(a) //&& l.lit_in(c) && 
        //(@a)[@l.idx] === AssignedState::Unset ==>
         //eventually_sat_formula_inner((@a).set(@l.idx, AssignedState::Positive), f)
    }
    pearlite! {
        compatible_inner(@a, (@a).set(@l.idx, AssignedState::Positive))
    };
    */
    /*
    pearlite! {
        eventually_sat_formula_inner(@a, f) && c.unit(a) ==>
            (forall<i: Int> 0 <= i && i < (@c).len() && (@a)[@(@c)[i].idx] === AssignedState::Unset &&
            eventually_sat_formula_inner((@a).set(@(@c)[i].idx, AssignedState::Positive), f) &&
            eventually_sat_formula_inner((@a).set(@(@c)[i].idx, AssignedState::Negative), f)
        )
    }
}
    */

#[logic]
/*
#[requires(c.unit(a))]
#[requires(0 <= (@l.idx) && (@l.idx) < (@a).len())]  
#[requires(l.lit_in(c))]
#[requires((@a)[@l.idx] === AssignedState::Unset)]
#[requires(l.polarity)]
#[requires(eventually_sat_formula_inner(@a, f))]
//#[ensures(c.sat(a))] // reencode
#[ensures(eventually_sat_formula_inner((@a).set(@l.idx, AssignedState::Positive), f))]
*/
pub fn lemma_pos3(a: Assignments, f: Formula, l: Lit, c: Clause) -> bool{
    pearlite! {
        eventually_sat_formula_inner(@a, f)&& c.unit(a) && l.lit_in(c) && 
        0 <= (@l.idx) && (@l.idx) < (@a).len() && l.polarity &&
        (@a)[@l.idx] === AssignedState::Unset ==>
        //eventually_sat_formula_inner((@a).set(@l.idx, AssignedState::Positive), f)
        sat_clause_inner((@a).set(@l.idx, AssignedState::Positive), c)
    }
}

#[logic]
pub fn lemma_pos(a: Assignments, f: Formula, c: Clause) -> bool{
    pearlite! {
        (eventually_sat_formula_inner(@a, f) && c.unit(a) &&
        (@a)[@unit_get_literal(c, a).idx] === AssignedState::Unset) ==>
        sat_clause_inner((@a).set(@unit_get_literal(c, a).idx, bool_to_assignedstate(unit_get_literal(c, a).polarity)), c) //==>
        //eventually_sat_formula_inner((@a).set(@unit_get_literal(c,a).idx, bool_to_assignedstate(unit_get_literal(c,a).polarity)), f)
        //eventually_sat_formula_inner((@a).set(@l.idx, bool_to_assignedstate(unit_get_literal(c,a).polarity)), f)
    }
}

#[logic]
#[ensures(result === !b)]
fn flipbool(b: bool) -> bool {
    !b
}

// Why the fuck is this proving
#[logic]
pub fn lemma_set_opposite(a: Assignments, f: Formula, c: Clause) -> bool{
    pearlite! {
        (eventually_sat_formula_inner(@a, f) && c.unit(a) &&
        (@a)[@unit_get_literal(c, a).idx] === AssignedState::Unset) ==>
        sat_clause_inner((@a).set(@unit_get_literal(c, a).idx, bool_to_assignedstate(flipbool(unit_get_literal(c, a).polarity))), c) //==>
        //eventually_sat_formula_inner((@a).set(@unit_get_literal(c,a).idx, bool_to_assignedstate(unit_get_literal(c,a).polarity)), f)
        //eventually_sat_formula_inner((@a).set(@l.idx, bool_to_assignedstate(unit_get_literal(c,a).polarity)), f)
    }
}

// Like how is this proving for both false and true?
#[logic]
pub fn lemma_set_test(a: Assignments, f: Formula, c: Clause) -> bool{
    pearlite! {
        (eventually_sat_formula_inner(@a, f) && c.unit(a) &&
        (@a)[@unit_get_literal(c, a).idx] === AssignedState::Unset) ==>
        sat_clause_inner((@a).set(@unit_get_literal(c, a).idx, bool_to_assignedstate(false)), c) //==>
        //eventually_sat_formula_inner((@a).set(@unit_get_literal(c,a).idx, bool_to_assignedstate(unit_get_literal(c,a).polarity)), f)
        //eventually_sat_formula_inner((@a).set(@l.idx, bool_to_assignedstate(unit_get_literal(c,a).polarity)), f)
    }
}

#[logic]
pub fn lemma_sat(a: Assignments, f: Formula, c: Clause) -> bool{
    pearlite! {
        c.unit(a) && eventually_sat_formula_inner(@a, f) && sat_clause_inner((@a).set(@unit_get_literal(c, a).idx, bool_to_assignedstate(unit_get_literal(c, a).polarity)), c) ==>
        eventually_sat_formula_inner((@a).set(@unit_get_literal(c,a).idx, bool_to_assignedstate(unit_get_literal(c,a).polarity)), f)
    }
}

#[logic]
pub fn has_to_assign(c: Clause, a: Assignments) -> bool{
    pearlite! {
        c.unit(a) === sat_clause_inner((@a).set(@unit_get_literal(c, a).idx, bool_to_assignedstate(unit_get_literal(c, a).polarity)), c)
    }
}

#[predicate]
pub fn sats_clause(a: Assignments, c: Clause) -> bool {
    pearlite! {
        c.unsat(a) ==> true
    }
}

#[logic]
pub fn lemma_pos2(a: Assignments, f: Formula, l: Lit, c: Clause) -> bool{
    pearlite! {
        eventually_sat_formula_inner(@a, f)&& c.unit(a) && l.lit_in(c) && 
        0 <= (@l.idx) && (@l.idx) < (@a).len() &&
        (@a)[@l.idx] === AssignedState::Unset ==>
        eventually_sat_formula_inner((@a).set(@l.idx, AssignedState::Positive), f)
    }
}


#[logic]
fn lemma_assign_unit2(c: Clause, f: Formula, a: Assignments) -> bool{
    pearlite! {
        eventually_sat_formula_inner(@a, f) && c.unit(a) ==>
          (forall<i: Int> 0 <= i && i < (@c).len() && (@a)[@(@c)[i].idx] === AssignedState::Unset &&
            eventually_sat_formula_inner((@a).set(@(@c)[i].idx, bool_to_assignedstate((@c)[i].polarity)), f) &&
            eventually_unsat_formula_inner((@a).set(@(@c)[i].idx, bool_to_assignedstate_negated((@c)[i].polarity)), f)
        )
    }
}

#[logic]
#[requires(0 <= ix && ix < a.len())]
#[requires(a[ix] === AssignedState::Unset)]
#[requires(eventually_unsat_formula_inner(a.set(ix, AssignedState::Positive), f))]
#[requires(eventually_unsat_formula_inner(a.set(ix, AssignedState::Negative), f))]
#[ensures(eventually_unsat_formula_inner(a, f))]
fn lemma_eventually_assigned(a: Seq<AssignedState>, ix: Int, f: Formula) {
    compatible_inner(a, a.set(ix, AssignedState::Positive));
    compatible_inner(a, a.set(ix, AssignedState::Negative));
}


#[logic]
#[requires(0 <= ix && ix < a.len())]
#[requires(eventually_unsat_formula_inner(a, f))]
#[requires(a[ix] === AssignedState::Unset)]
#[ensures(eventually_unsat_formula_inner(a.set(ix, AssignedState::Positive), f))]
#[ensures(eventually_unsat_formula_inner(a.set(ix, AssignedState::Negative), f))]
fn lemma_opp(a: Seq<AssignedState>, ix: Int, f: Formula) {
    compatible_inner(a, a.set(ix, AssignedState::Positive));
    compatible_inner(a, a.set(ix, AssignedState::Negative));
}


#[logic]
pub fn lemma_dont_matter(f: Formula, a: Assignments) -> bool{
    pearlite! {
        eventually_unsat_formula_inner(@a, f) ==>
        (forall<j: Int> 0 <= j && j < (@a).len() && (@a)[j] === AssignedState::Unset ==>
            (eventually_unsat_formula_inner((@a).set(j, AssignedState::Positive), f) &&
            eventually_unsat_formula_inner((@a).set(j, AssignedState::Negative), f)))
    }
}

#[logic]
pub fn lemma_dont_matter_two(a: Assignments, f: Formula, ix: Int) -> bool{
    pearlite! {
        (@a)[ix] === AssignedState::Unset && eventually_unsat_formula_inner(@a, f) ==>
            (eventually_unsat_formula_inner((@a).set(ix, AssignedState::Positive), f) &&
            eventually_unsat_formula_inner((@a).set(ix, AssignedState::Negative), f))
    }
}

#[logic]
pub fn lemma_both_unsat_whole_unsat(a: Assignments, f: Formula, ix: Int) -> bool{
    pearlite! {
            (eventually_unsat_formula_inner((@a).set(ix, AssignedState::Positive), f) &&
            eventually_unsat_formula_inner((@a).set(ix, AssignedState::Negative), f)) ==>
        eventually_unsat_formula_inner(@a, f)
    }
}

#[logic]
pub fn lemma_one_sat_whole_sat(a: Assignments, f: Formula, ix: Int) -> bool{
    pearlite! {
        (eventually_sat_formula_inner((@a).set(ix, AssignedState::Positive), f) ||
        eventually_sat_formula_inner((@a).set(ix, AssignedState::Negative), f)) ==>
        eventually_sat_formula_inner(@a, f)
    }
}