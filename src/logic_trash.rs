/*
#[logic]
#[requires(c.no_duplicate_indexes())]
#[requires(c2.no_duplicate_indexes())]
#[requires(c3.resolvent_of_idx(c, c2, idx))]
#[requires((@c2)[k].is_opp((@c)[m]))]
#[ensures(c3.resolvent_of(c, c2, k, m))]
pub fn lemma_gives_res_of_idx(c: Clause, c2: Clause, c3: Clause, idx: Int, k: Int, m: Int) {}
*/

//#[trusted] // OK
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(c2.in_formula_inner(f))]
#[requires(c3.resolvent_of_idx(c, c2, idx))]
#[requires(eventually_sat_complete_no_ass(f))]
#[ensures(eventually_sat_complete_no_ass(((f.0).push(c3), f.1)))]
pub fn lemma_sat_gives_sat_idx(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, idx: Int) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    //lemma_sub_clause_not_sat2(c, c2, c3, a);
    //lemma_sub_clause_sat2(c, c2, c3, a, idx);
}

/*
#[trusted] // OK
#[logic]
#[requires(exists<idx: Int> 0 <= idx && idx < (@a).len() &&
    c3.resolvent_of_idx(c, c2, idx))]
#[requires(!c.sat(a))]
#[requires(!c2.sat(a))]
#[ensures(!c3.sat(a))]
pub fn lemma_sub_clause_not_sat2(c: Clause, c2: Clause, c3: Clause, a: Assignments) {}

// Requires knowledge of the idx of the conflict literal
//#[trusted] // OK
#[logic]
#[requires(c3.resolvent_of(c, c2, k, m))]
#[requires(c.sat(a))]
#[requires(c2.sat(a))]
#[ensures(c3.sat(a))]
pub fn lemma_sub_clause_sat(c: Clause, c2: Clause, c3: Clause, a: Assignments, k: Int, m: Int) {}

#[trusted] // OK
#[logic]
#[requires(c.invariant((@a).len()))]
#[requires(c2.invariant((@a).len()))]
#[requires(exists<idx: Int> 0 <= idx && idx < (@a).len() &&
    c3.resolvent_of_idx(c, c2, idx))]
#[requires(c.sat(a))]
#[requires(c2.sat(a))]
#[ensures(c3.sat(a))]
pub fn lemma_sub_clause_sat3(c: Clause, c2: Clause, c3: Clause, a: Assignments) {}

#[trusted] // OK
#[logic]
#[requires(c.invariant((@a).len()))]
#[requires(c2.invariant((@a).len()))]
#[requires(c3.resolvent_of_idx(c, c2, idx))]
#[requires(c.sat(a))]
#[requires(c2.sat(a))]
#[ensures(c3.sat(a))]
pub fn lemma_sub_clause_sat2(c: Clause, c2: Clause, c3: Clause, a: Assignments, idx: Int) {}
*/
/*
#[logic]
#[requires(formula_invariant(f))]
#[requires(equisat_extension_inner(c, f))]
#[requires(equisat_extension_inner(c2, f))]
#[requires(c3.resolvent_of(c, c2, k, m))]
#[ensures(equisat_extension_inner(c3, f))]
//#[ensures(equisat_compatible_inner(f, (f.0.push(c3), f.1)))]
pub fn lemma_resolvent_of_equisat_extension_is_equisat2(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, k: Int, m: Int, a: Assignments) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    lemma_not_sat_gives_not_sat(f, c, c2, c3, k, m, a);
    lemma_sat_gives_sat(f, c, c2, c3, k, m, a);
    lemma_extended_formula_is_equisat_compatible(f, c, c2, c3, k, m, a);
    lemma_resolvent_of_equisat_extension_is_equisat(f, c, c2, c3, k, m, a);
}
*/

/*
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(equisat_extension_inner(c2, f))]
//#[requires(c3.resolvent_of(c, c2, k, m))]
#[requires(c3.resolvent_of_idx(c, c2, idx))]
#[ensures(equisat_extension_inner(c3, f))]
//#[ensures(equisat_compatible_inner(f, (f.0.push(c3), f.1)))]
pub fn lemma_resolvent_of_equisat_extension_is_equisat4(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, idx: Int, c_index: Int, a: Assignments) {
    lemma_res_idx_to_km(c, c2, c3, idx, a);
    //lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    //lemma_not_sat_gives_not_sat(f, c, c2, c3, k, m, a);
    //lemma_sat_gives_sat(f, c, c2, c3, k, m, a);
    //lemma_extended_formula_is_equisat_compatible(f, c, c2, c3, k, m, a);
}
*/

/*
//#[trusted] // OK
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(equisat_extension_inner(c2, f))]
#[requires(c3.resolvent_of_idx(c, c2, idx))]
#[ensures(equisat_extension_inner(c3, f))]
//#[ensures(equisat_compatible_inner(f, (f.0.push(c3), f.1)))]
pub fn lemma_resolvent_of_equisat_extension_is_equisat_new(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, idx: Int, a: Assignments) {
    lemma_res_idx_to_km(c, c2, c3, idx, a);
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    lemma_not_sat_gives_not_sat(f, c, c2, c3, k, m, a);
    lemma_sat_gives_sat(f, c, c2, c3, k, m, a);
    lemma_extended_formula_is_equisat_compatible2(f, c, c2, c3, idx, a);
}
*/

/*
// Does not prove
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(equisat_extension_inner(c2, f))]
#[requires(c3.resolvent_of_idx(c, c2, idx))]
#[ensures(equisat_extension_inner(c3, f))]
//#[ensures(equisat_compatible_inner(f, (f.0.push(c3), f.1)))]
pub fn lemma_resolvent_of_equisat_extension_is_equisat2(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, idx: Int, a: Assignments) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    lemma_not_sat_gives_not_sat2(f, c, c2, c3, idx, a);
    lemma_sat_gives_sat2(f, c, c2, c3, idx, a);
    lemma_extended_formula_is_equisat_compatible2(f, c, c2, c3, idx, a);
}
*/

//#[trusted] // OK
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(c2.in_formula_inner(f))]
//#[requires(equisat_extension_inner(c2, f))]
#[requires(c3.resolvent_of_idx2(c, c2, idx, c_idx))]
#[requires(eventually_sat_complete_no_ass(f))]
#[ensures(eventually_sat_complete_no_ass(((f.0).push(c3), f.1)))]
pub fn lemma_sat_gives_sat_double_index(
    f: (Seq<Clause>, Int),
    c: Clause,
    c2: Clause,
    c3: Clause,
    idx: Int,
    c_idx: Int,
) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    //lemma_sub_clause_not_sat2(c, c2, c3, a);
    //lemma_sub_clause_sat2(c, c2, c3, a, idx);
}

//#[trusted] // OK
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(c2.in_formula_inner(f))]
#[requires(c3.resolvent_of_idx2(c, c2, idx, c_idx))]
//#[ensures(equisat_compatible_inner(f, (f.0.push(c3), f.1)))]
#[ensures(equisat_extension_inner(c3, f))]
pub fn lemma_extended_formula_is_equisat_compatible_new(
    f: (Seq<Clause>, Int),
    c: Clause,
    c2: Clause,
    c3: Clause,
    idx: Int,
    c_idx: Int,
) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    //lemma_not_sat_gives_not_sat2(f, c, c2, c3, idx, a);
    //lemma_sat_gives_sat2(f, c, c2, c3, idx, a);
}

//#[trusted] // OK
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(c2.in_formula_inner(f))]
#[requires(c3.resolvent_of_idx(c, c2, idx))]
//#[ensures(equisat_compatible_inner(f, (f.0.push(c3), f.1)))]
#[ensures(equisat_extension_inner(c3, f))]
pub fn lemma_extended_formula_is_equisat_compatible2(
    f: (Seq<Clause>, Int),
    c: Clause,
    c2: Clause,
    c3: Clause,
    idx: Int,
    a: Assignments,
) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    //lemma_not_sat_gives_not_sat2(f, c, c2, c3, idx, a);
    //lemma_sat_gives_sat2(f, c, c2, c3, idx, a);
}

//#[trusted]
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(equisat_extension_inner(c2, f))]
#[requires(c3.resolvent_of_idx2(c, c2, idx, c_idx))]
#[ensures(equisat_extension_inner(c3, f))]
//#[ensures(equisat_compatible_inner(f, (f.0.push(c3), f.1)))]
pub fn lemma_resolvent_of_equisat_extension_is_equisat_new(
    f: (Seq<Clause>, Int),
    c: Clause,
    c2: Clause,
    c3: Clause,
    idx: Int,
    c_idx: Int,
) {
    lemma_eq_formulas(f, (f.0.push(c3), f.1), c3);
    lemma_not_sat_gives_not_sat(f, c, c2, c3);
    lemma_sat_gives_sat_double_index(f, c, c2, c3, idx, c_idx);
    lemma_extended_formula_is_equisat_compatible_new(f, c, c2, c3, idx, c_idx);
}

#[trusted] // OK
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(c2.in_formula_inner(f))]
#[requires(c3.resolvent_of(c, c2, k, m))]
#[ensures(equisat_extension_inner(c, f))]
pub fn lemma_resolvent_of_in_is_equisat(
    f: (Seq<Clause>, Int),
    c: Clause,
    c2: Clause,
    c3: Clause,
    k: Int,
    m: Int,
    a: Assignments,
) {
    lemma_extended_formula_is_equisat_compatible(f, c, c2, c3, k, m);
}

#[trusted] // OK
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(c2.in_formula_inner(f))]
#[requires(c3.resolvent_of_idx(c, c2, idx))]
#[ensures(equisat_extension_inner(c, f))]
pub fn lemma_resolvent_of_in_is_equisat2(
    f: (Seq<Clause>, Int),
    c: Clause,
    c2: Clause,
    c3: Clause,
    idx: Int,
    a: Assignments,
) {
    lemma_extended_formula_is_equisat_compatible2(f, c, c2, c3, idx, a);
}

//#[trusted]
/*
#[logic]
#[requires(c.invariant((@a).len()))]
#[requires(c2.invariant((@a).len()))]
#[requires(c3.resolvent_of(c, c2, k, m))]
#[ensures(c3.resolvent_of_idx(c, c2, @(@c2)[k].idx))]
pub fn lemma_res_km_idx(c: Clause, c2: Clause, c3: Clause, k: Int, m: Int, a: Assignments) {}
*/

// Slow, but should be easy to make faster
#[trusted] // OK
#[logic]
#[requires(c.invariant((@a).len()))]
#[requires(c2.invariant((@a).len()))]
#[requires(c3.resolvent_of_idx(c, c2, idx))]
#[ensures(exists<k: Int, m: Int> c3.resolvent_of(c, c2, k, m))]
pub fn lemma_res_idx_to_km(c: Clause, c2: Clause, c3: Clause, idx: Int, a: Assignments) {}

// trail garbo
#[logic]
#[requires(a.invariant(f))]
#[requires(f.invariant())]
#[requires(trail_invariant(v, f))]
#[requires(crefs_in_range(v, f))]
#[requires(lit.invariant(@f.num_vars))]
//#[requires(unset((@a)[@lit.idx]))]
#[requires(v.len() === 2)]
#[requires(long_are_post_unit_inner(v, f, @a))]
/*
#[requires(forall<i: Int> 0 <= i && i < v.len() ==>
    match v[i].reason {
        Reason::Long(k) => !lit.lit_in((@f.clauses)[@k]),
        _ => true,
    }
)]
*/
#[requires(forall<i: Int> 0 <= i && i < (@f.clauses).len() && i != cref ==> 
    (@f.clauses)[i].post_unit_inner(@a) ==> 
    (@f.clauses)[i].post_unit_inner((@a).set(@lit.idx, 3u8))
)]
#[requires(forall<i: Int> 0 <= i && i < (@f.clauses).len() && i != cref ==> 
    (!(@f.clauses)[i].post_unit_inner(@a) || !lit.lit_idx_in((@f.clauses)[i]))
)]
/*
#[requires(forall<i: Int> 0 <= i && i < v.len() ==>
    v[i].lit.idx != lit.idx
)]
#[requires(forall<i: Int> 0 <= i && i < v.len() ==>
    !(v[i].lit === lit)
)]
*/
/*
#[requires(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==>
    (@f.clauses)[i].post_unit_inner(@a) !lit.lit_in((@f.clauses)[@k] ==>
    (@f.clauses)[i].post_unit_inner((@a).set(@lit.idx, 3u8))
)]
*/
/*
#[requires(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==>
    (@f.clauses)[i].post_unit_inner(@a) ==>
    (@f.clauses)[i].post_unit_inner((@a).set(@lit.idx, 0u8))
)]
*/
#[ensures(long_are_post_unit_inner(v, f, (@a).set(@lit.idx, 3u8)))]
//#[ensures(long_are_post_unit_inner(v, f, (@a).set(@lit.idx, 0u8)))]

fn lemma_assign_unwrapped(v: Seq<Step>, f: Formula, a: Assignments, lit: Lit, cref: Int) {}

/*
forall<j: Int> 0 <= j && j < trail.len() ==> match
trail[j].reason {
    Reason::Long(k) => { clause_post_with_regards_to_inner((@f.clauses)[@k], a, j) },
        _ => true,
    }
    */
//#[trusted]
#[logic]
#[requires(t.invariant(f))]
#[requires(t.lit_not_in_less(f))]
#[requires(t.lit_is_unique())]
#[requires((@t.trail).len() === 2)]
#[requires(l === (@t.trail)[(@t.trail).len() - 1].lit)]
#[ensures(forall<i: Int> 0 <= i && i < (@t.trail).len() - 1 ==>
    !l.lit_idx_in((@f.clauses)[@(@t.trail)[i].lit.idx])
)]
fn lemma_last_doesnt_exist_anywhere_else(t: NTrail, f: Formula, l: Lit) {
    t.lit_not_in_less(f);
    t.lit_is_unique();
}

//#[trusted] // OK
#[logic]
#[requires(a.invariant(f))]
#[requires(f.invariant())]
#[requires(trail_invariant(v, f))]
#[requires(crefs_in_range(v, f))]
#[requires(lit.invariant(@f.num_vars))]
#[requires(unset((@a)[@lit.idx]))]
#[requires(long_are_post_unit_inner(v, f, @a))]
#[requires(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    (@f.clauses)[i].post_unit_inner(@a) ==> 
    (@f.clauses)[i].post_unit_inner((@a).set(@lit.idx, 1u8))
)]
#[requires(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    (@f.clauses)[i].post_unit_inner(@a) ==> 
    (@f.clauses)[i].post_unit_inner((@a).set(@lit.idx, 0u8)) 
)]
#[ensures(long_are_post_unit_inner(v, f, (@a).set(@lit.idx, 1u8)))]
#[ensures(long_are_post_unit_inner(v, f, (@a).set(@lit.idx, 0u8)))]
fn lemma_assign_newest(v: Seq<Step>, f: Formula, a: Assignments, lit: Lit) {}

// There is no chance in hell this could ever check out lol.
// Lacking preconds + there is no connection between trail completeness and post units
// (which btw is unachievable)
//#[trusted] // OK
#[logic]
//#[requires(trail_invariant(v, f))]
//#[requires(crefs_in_range(v, f))]
//#[requires(a.invariant(f))]
#[requires(t.invariant(f))]
#[requires(f.invariant())]
#[requires(lit.invariant(@f.num_vars))]
//#[requires(unset((@a)[@lit.idx]))]
#[requires(forall<i: Int> 0 <= i && i < (@t.trail).len() ==>
    !lit.lit_idx_in((@f.clauses)[@(@t.trail)[i].lit.idx])
)]
#[ensures(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    (@f.clauses)[i].post_unit_inner(@t.assignments) ==> 
    (@f.clauses)[i].post_unit_inner((@t.assignments).set(@lit.idx, 3u8))
)]
fn lemma_assign_maintains_post_att(t: NTrail, f: Formula, lit: Lit) {}

//#[trusted] // OK
#[logic]
#[requires(t.invariant(f))]
#[requires(t.lit_not_in_less(f))]
#[requires(t.lit_is_unique())]
#[requires((@t.trail).len() > 2)]
//#[requires((@t.trail).len() > 0)]
#[requires(long_are_post_unit_inner(@t.trail, f, @t.assignments))]
#[requires(t.is_backtrackable(f))]
#[ensures(long_are_post_unit_inner(pop(@t.trail), f, 
(@t.assignments).set(@(@t.trail)[(@t.trail).len() - 1].lit.idx, 3u8)))]
//#[ensures(is_backtrackable_inner(
//    pop(@t.trail),(@t.assignments).set(@(@t.trail)[(@t.trail).len() - 1].lit.idx, 3u8), f))]
fn lemma_backtrack_ok_with_backtrackable(t: NTrail, f: Formula, l: Lit) {}

#[logic]
#[requires(t.invariant(f))]
#[requires(t.lit_not_in_less(f))]
#[requires(t.lit_is_unique())]
#[requires((@t.trail).len() >= 2)]
//#[requires((@t.trail).len() > 0)]
#[requires(long_are_post_unit_inner(@t.trail, f, @t.assignments))]
#[requires(t.is_backtrackable(f))]
#[requires(long_are_post_unit_inner(pop(@t.trail), f, 
(@t.assignments).set(@(@t.trail)[(@t.trail).len() - 1].lit.idx, 3u8)))]
#[ensures(is_backtrackable_inner(
    pop(@t.trail),(@t.assignments).set(@(@t.trail)[(@t.trail).len() - 1].lit.idx, 3u8), f))]
fn lemma_backtrack_ok2(t: NTrail, f: Formula, l: Lit) {
    lemma_backtrack_ok(t, f, l);
    lemma_backtrack_ok_len2(t, f, l);
    lemma_backtrack_ok_len3(t, f, l);
}
#[logic]
#[requires(t.invariant(f))]
#[requires(t.lit_not_in_less(f))]
#[requires(t.lit_is_unique())]
#[requires((@t.trail).len() === 2)]
#[requires(long_are_post_unit_inner(@t.trail, f, @t.assignments))]
#[requires(t.is_backtrackable(f))]
#[ensures(long_are_post_unit_inner(pop(@t.trail), f, 
(@t.assignments).set(@(@t.trail)[(@t.trail).len() - 1].lit.idx, 3u8)))]
#[ensures(is_backtrackable_inner(
    pop(@t.trail),(@t.assignments).set(@(@t.trail)[(@t.trail).len() - 1].lit.idx, 3u8), f))]
fn lemma_backtrack_ok_len2(t: NTrail, f: Formula, l: Lit) {
    lemma_backtrack_ok(t, f, l);
}

#[logic]
#[requires(t.invariant(f))]
#[requires(t.lit_not_in_less(f))]
#[requires(t.lit_is_unique())]
#[requires((@t.trail).len() === 3)]
#[requires(long_are_post_unit_inner(@t.trail, f, @t.assignments))]
#[requires(t.is_backtrackable(f))]
#[ensures(long_are_post_unit_inner(pop(@t.trail), f, 
(@t.assignments).set(@(@t.trail)[(@t.trail).len() - 1].lit.idx, 3u8)))]
#[ensures(is_backtrackable_inner(
    pop(@t.trail),(@t.assignments).set(@(@t.trail)[(@t.trail).len() - 1].lit.idx, 3u8), f))]
fn lemma_backtrack_ok_len3(t: NTrail, f: Formula, l: Lit) {
    lemma_backtrack_ok(t, f, l);
    lemma_backtrack_ok_len2(t, f, l);
}

#[logic]
#[requires(a.invariant(f))]
#[requires(f.invariant())]
#[requires(lit.invariant(@f.num_vars))]
#[requires(t.invariant(f))]
#[ensures(forall<i: Int> 0 <= i && i < (@t.trail).len() ==> 
match (@t.trail)[i].reason {
    Reason::Long(k) => ((@f.clauses)[@k].post_unit_inner(@a) && !lit.lit_idx_in((@f.clauses)[@k])) ==> 
                (@f.clauses)[@k].post_unit_inner((@a).set(@lit.idx, 3u8)),
    _ => true,
}
)]
fn lemma_trail_post_old(f: Formula, a: Assignments, lit: Lit, t: NTrail) {}

#[predicate]
pub fn is_backtrackable(self, f: Formula) -> bool {
    pearlite! {
        is_backtrackable_inner(@self.trail, @self.assignments, f)
    }
}

// This doesn't work because the slicing of the trail is nonesense
/*
#[predicate]
pub fn is_backtrackable_forall(self, f: Formula) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < (@self.trail).len() ==>
            is_backtrackable_inner(@self.trail.subsequence(0, i), @self.assignments, f)
        //is_backtrackable_inner(@self.trail, @self.assignments, f)
    }
}
*/

//#[trusted] // OK
#[logic]
#[requires(a.invariant(f))]
#[requires(f.invariant())]
#[requires(lit.invariant(@f.num_vars))]
#[ensures(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    ((@f.clauses)[i].post_unit_inner(@a) && !lit.lit_idx_in((@f.clauses)[i])) ==> 
    (@f.clauses)[i].post_unit_inner((@a).set(@lit.idx, 3u8))
)]
fn lemma_assign_maintains_test(f: Formula, a: Assignments, lit: Lit) {}

#[trusted] // OK
#[logic]
#[requires(c.unit_inner(a))]
#[ensures(c.unit_inner2(a))]
fn lemma_unit_eq(c: Clause, a: Seq<AssignedState>) {}

#[trusted] // OK
#[logic]
#[requires(c.unit_inner2(a))]
#[requires(c.vars_in_range(a.len()))]
#[ensures(c.unit_inner(a))]
fn lemma_unit_eq2(c: Clause, a: Seq<AssignedState>) {}

/*
#[logic]
#[variant(j-i)]
fn count(i: Int, j: Int, t: Seq<Lit>, lf: Int) -> Int {
    pearlite! {
        if i >= j { 0 } else {
            if @t[j-1].idx === lf {
                count(i,j-1,t, lf) + 1
            } else {
                count(i,j-1,t, lf)
            }
        }
    }
}
*/

/*
#[logic]
#[requires(no_duplicate_indexes_inner(v))]
#[requires(v.permutation_of(v2))]
#[ensures(no_duplicate_indexes_inner(v2))]
fn lemma_no_dups_permut(v: Seq<Lit>, v2: Seq<Lit>) {}
*/
