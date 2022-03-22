
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
pub fn lemma_sat_gives_sat_double_index(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, idx: Int, c_idx: Int) {
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
pub fn lemma_extended_formula_is_equisat_compatible_new(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, idx: Int, c_idx: Int) {
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
pub fn lemma_extended_formula_is_equisat_compatible2(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, idx: Int, a: Assignments) {
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
pub fn lemma_resolvent_of_equisat_extension_is_equisat_new(f: (Seq<Clause>, Int), c: Clause, c2: Clause, c3: Clause, idx: Int, c_idx: Int) {
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
pub fn lemma_resolvent_of_in_is_equisat(f: (Seq<Clause>, Int),  c: Clause, c2: Clause, c3: Clause, k: Int, m: Int, a: Assignments) {
    lemma_extended_formula_is_equisat_compatible(f,  c, c2, c3, k, m);
}


#[trusted] // OK
#[logic]
#[requires(formula_invariant(f))]
#[requires(c.in_formula_inner(f))]
#[requires(c2.in_formula_inner(f))]
#[requires(c3.resolvent_of_idx(c, c2, idx))]
#[ensures(equisat_extension_inner(c, f))] 
pub fn lemma_resolvent_of_in_is_equisat2(f: (Seq<Clause>, Int),  c: Clause, c2: Clause, c3: Clause, idx: Int, a: Assignments) {
    lemma_extended_formula_is_equisat_compatible2(f,  c, c2, c3, idx, a);
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