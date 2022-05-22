// Just swap missing (15.04, 16:31)
extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::logic::Ghost;
use creusot_contracts::*;

use crate::{formula::*, lit::*, trail::*, watches::*};

use crate::logic::{
    logic::*,
    logic_clause::*,
    logic_trail::*, //tmp
};

// OK
#[cfg_attr(feature = "trust_unit", trusted)]
#[maintains((mut f).invariant())]
#[maintains(trail.invariant(mut f))]
#[maintains((mut watches).invariant(mut f))]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(lit.index_logic() < @f.num_vars)]
//#[requires((@trail.trail).len() > 0)]
#[requires(@cref < (@f.clauses).len())]
#[requires(2 <= @k && @k < (@(@f.clauses)[@cref]).len())]
#[requires((@(@f.clauses)[@cref]).len() > 2)]
#[requires((@(@watches.watches)[lit.to_watchidx_logic()]).len() > @j)]
#[ensures(@f.num_vars == @(^f).num_vars)]
#[ensures(f.equisat(^f))]
#[ensures((@f.clauses).len() == (@(^f).clauses).len())]
#[ensures(match result {
    Ok(_) => true,
    Err(_) => (@(@(^f).clauses)[@cref])[@k].unsat(trail.assignments) && ^f == *f && *watches == ^watches
})]
#[ensures((@(@(^f).clauses)[@cref]).len() == (@(@f.clauses)[@cref]).len())] // ADDDED, will need proving
fn unit_prop_check_rest(
    f: &mut Formula, trail: &Trail, watches: &mut Watches, cref: usize, j: usize, k: usize, lit: Lit,
) -> Result<(), ()> {
    let curr_lit = f.clauses[cref].rest[k];
    if curr_lit.lit_unset(&trail.assignments) || curr_lit.lit_sat(&trail.assignments) {
        // Can swap to !unsat
        if f.clauses[cref].rest[0].index() == lit.index() {
            // First
            swap(f, trail, watches, cref, k, 0);
            update_watch(f, trail, watches, cref, j, 0, lit);
        } else {
            swap(f, trail, watches, cref, k, 1);
            update_watch(f, trail, watches, cref, j, 1, lit);
        }
        return Ok(()); // dont increase j
    }
    return Err(());
}

#[cfg_attr(feature = "trust_unit", trusted)]
#[maintains((*trail).invariant(mut f))]
#[maintains((mut f).invariant())]
#[maintains((*watches).invariant(mut f))]
#[requires((@(@f.clauses)[@cref]).len() >= 2)]
#[requires((@(@f.clauses)[@cref]).len() > @j)]
#[requires((@(@f.clauses)[@cref]).len() > @k)]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(@cref < (@f.clauses).len())]
#[ensures(@f.num_vars == @(^f).num_vars)]
#[ensures((@f.clauses).len() == (@(^f).clauses).len())]
#[ensures((@(@f.clauses)[@cref]).len() == (@(@(^f).clauses)[@cref]).len())]
#[ensures(f.equisat(^f))]
fn swap(f: &mut Formula, trail: &Trail, watches: &Watches, cref: usize, j: usize, k: usize) {
    let old_f = Ghost::record(&f);
    proof_assert!(no_duplicate_indexes_inner(@(@f.clauses)[@cref]));
    proof_assert!(long_are_post_unit_inner(@trail.trail, *f, @trail.assignments) && true);
    f.clauses[cref].rest.swap(j, k);
    proof_assert!(lemma_swap_maintains_post_unit(((@(@old_f).clauses)[@cref]), ((@f.clauses)[@cref]), @j, @k, trail.assignments); true);
    proof_assert!(vars_in_range_inner(@(@f.clauses)[@cref], @f.num_vars));
    proof_assert!(no_duplicate_indexes_inner(@(@f.clauses)[@cref]));
    proof_assert!(long_are_post_unit_inner(@trail.trail, *f, @trail.assignments));
    proof_assert!(^@old_f == ^f);
}

/*
// OK
//#[cfg_attr(feature = "trust_unit", trusted)]
#[maintains((*trail).invariant(mut f))]
#[maintains((mut f).invariant())]
#[maintains((*watches).invariant(mut f))]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(@cref < (@f.clauses).len())]
#[requires((@(@f.clauses)[@cref]).len() >= 2)]
#[ensures(@f.num_vars == @(^f).num_vars)]
#[ensures((@f.clauses).len() == (@(^f).clauses).len())]
#[ensures((@(@f.clauses)[@cref]).len() == (@(@(^f).clauses)[@cref]).len())]
#[ensures(f.equisat(^f))]
fn swap_zero_one(f: &mut Formula, trail: &Trail, watches: &Watches, cref: usize) {
    let old_f = Ghost::record(&f);
    proof_assert!(no_duplicate_indexes_inner(@(@f.clauses)[@cref]));
    proof_assert!(long_are_post_unit_inner(@trail.trail, *f, @trail.assignments) && true);
    f.clauses[cref].rest.swap(0, 1);
    proof_assert!(lemma_swap_maintains_post_unit(((@(@old_f).clauses)[@cref]), ((@f.clauses)[@cref]), 0, 1, trail.assignments); true);
    proof_assert!(vars_in_range_inner(@(@f.clauses)[@cref], @f.num_vars));
    proof_assert!(no_duplicate_indexes_inner(@(@f.clauses)[@cref]));
    proof_assert!(long_are_post_unit_inner(@trail.trail, *f, @trail.assignments));
    proof_assert!(^@old_f == ^f);
}
*/

// OK on Mac
#[cfg_attr(feature = "trust_unit", trusted)]
#[maintains((mut f).invariant())]
#[maintains((mut trail).invariant(mut f))]
#[maintains((mut watches).invariant(mut f))]
#[requires((@(@watches.watches)[lit.to_watchidx_logic()]).len() > @j)]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(lit.index_logic() < @f.num_vars)]
#[requires(watches.invariant(*f))]
#[requires(@cref < (@f.clauses).len())]
#[requires((@(@f.clauses)[@cref]).len() >= 2)]
#[ensures((^trail).decisions == trail.decisions)] // added
#[ensures(match result {
    Ok(true) => true,
    Ok(false) => (@(^trail).trail).len() == (@trail.trail).len(),
    Err(n) => @n < (@(^f).clauses).len() && (^f).unsat((^trail).assignments) && (@(^f).clauses)[@n].unsat((^trail).assignments),
})]
#[ensures(@f.num_vars == @(^f).num_vars)]
#[ensures(f.equisat(^f))]
fn unit_prop_do_outer(
    f: &mut Formula, trail: &mut Trail, watches: &mut Watches, cref: usize, lit: Lit, j: usize,
) -> Result<bool, usize> {
    let first_lit = f.clauses[cref].rest[0];
    if first_lit.lit_sat(&trail.assignments) {
        return Ok(true);
    }
    let second_lit = f.clauses[cref].rest[1];
    let old_f = Ghost::record(&f);
    if second_lit.lit_sat(&trail.assignments) {
        // We swap to make it faster the next time
        //swap_zero_one(f, trail, watches, cref, lit, j);
        swap(f, trail, watches, cref, 0, 1);
        return Ok(true);
    }
    // At this point we know that none of the watched literals are sat
    let mut k: usize = 2;
    let clause_len: usize = f.clauses[cref].rest.len();
    let old_trail = Ghost::record(&trail);
    let old_w = Ghost::record(&watches);
    #[invariant(k_bound, 2 <= @k && @k <= @clause_len)]
    #[invariant(watch_len, (@watches.watches).len() == (@(@old_w).watches).len())]
    #[invariant(watch_inv, watches.invariant(*f))]
    #[invariant(trail_inv, trail.invariant(*f))]
    #[invariant(f_equi, (@old_f).equisat(*f))]
    #[invariant(f_inv, f.invariant())]
    #[invariant(f_len, (@f.clauses).len() == (@(@old_f).clauses).len())]
    #[invariant(len_same, (@(@f.clauses)[@cref]).len() == @clause_len)]
    #[invariant(nvars_unch, @f.num_vars == @(@old_f).num_vars)]
    #[invariant(f_unch, f == @old_f)]
    #[invariant(w_unch, *watches == *@old_w)]
    #[invariant(dec_unch, (@trail.decisions) == (@(@old_trail).decisions))]
    #[invariant(proph_t, ^trail == ^@old_trail)]
    #[invariant(proph_f, ^f == ^@old_f)]
    #[invariant(proph_w, ^watches == ^@old_w)]
    #[invariant(uns, forall<m: Int> 2 <= m && m < @k ==> ((@(@f.clauses)[@cref])[m]).unsat(trail.assignments))]
    while k < clause_len {
        proof_assert!((@(@watches.watches)[lit.to_watchidx_logic()]).len() > @j);
        match unit_prop_check_rest(f, trail, watches, cref, j, k, lit) {
            Err(_) => {
                proof_assert!((@old_trail).decisions == trail.decisions);
                proof_assert!(*watches == *@old_w);
                proof_assert!(*f == *@old_f);
            }
            Ok(_) => {
                return Ok(false);
            }
        }
        k += 1;
    }
    proof_assert!((@old_trail).decisions == trail.decisions);
    // If we have gotten here, the clause is either all false or unit
    proof_assert!((@f.clauses)[@cref].unsat(trail.assignments) || ((@(@f.clauses)[@cref])[0]).unset(trail.assignments) || ((@(@f.clauses)[@cref])[1]).unset(trail.assignments));
    if first_lit.lit_unset(&trail.assignments) {
        //if f.clauses[cref].rest[0].lit_unset(&trail.assignments) {
        // zzTODOzz: Prove the runtime-check
        if second_lit.lit_unset(&trail.assignments) {
            return Ok(true);
        }
        proof_assert!(trail.invariant(*f));
        proof_assert!(!(@f.clauses)[@cref].unsat(trail.assignments));
        proof_assert!((@f.clauses)[@cref].unit(trail.assignments));
        let step = Step {
            lit: first_lit,
            //lit: f.clauses[cref].rest[0],
            decision_level: trail.decision_level(),
            reason: Reason::Long(cref),
        };

        trail.enq_assignment(step, f);
        proof_assert!(((@f.clauses)[@cref]).post_unit(trail.assignments) && true);
        proof_assert!(clause_post_with_regards_to_lit(((@f.clauses)[@cref]), trail.assignments, first_lit));
        return Ok(true);
    } else if second_lit.lit_unset(&trail.assignments) {
        //} else if f.clauses[cref].rest[1].lit_unset(&trail.assignments) {
        proof_assert!(!(@f.clauses)[@cref].unsat(trail.assignments) && true && true);
        proof_assert!((@f.clauses)[@cref].unit(trail.assignments));
        let step = Step { lit: second_lit, decision_level: trail.decision_level(), reason: Reason::Long(cref) };

        trail.enq_assignment(step, f);
        proof_assert!(((@f.clauses)[@cref]).post_unit(trail.assignments));
        proof_assert!(clause_post_with_regards_to_lit(((@f.clauses)[@cref]), trail.assignments, second_lit));
        // slowdown in swapping
        //f.clauses[cref].rest.swap(0,1);
        //proof_assert!((@f.clauses)[@cref].unit(*a) && true);
        /*
        proof_assert!(lemma_swap_clause_no_dups(((@(@old_f).clauses)[@cref]), ((@f.clauses)[@cref]), 0, 1); true);
        proof_assert!(lemma_swap_maintains_post_unit(((@(@old_f).clauses)[@cref]), ((@f.clauses)[@cref]), 0, 1, *a); true);
        // Not sure if this really helps, as we are sort of "short circuiting" the j
        proof_assert!(lemma_swap_maintains_post_with_regards_to(((@(@old_f).clauses)[@cref]), ((@f.clauses)[@cref]), 0, 1, *a, second_lit.index_logic()); true);
        // Can add a lemma here to make the formula invariant faster
        proof_assert!(lemma_permut_clause_in_formula_maintains_sat(*@old_f, *f, @cref); true);
        proof_assert!(lemma_permut_clause_in_formula_maintains_unsat(*@old_f, *f, @cref); true);
        */
        return Ok(true);
    } else {
        return Err(cref);
    }
}

// OK on Mac
#[cfg_attr(feature = "trust_unit", trusted)]
#[maintains((mut f).invariant())]
#[maintains((mut trail).invariant(mut f))]
#[maintains((mut watches).invariant(mut f))]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(lit.index_logic() < @f.num_vars)]
#[ensures(match result {
    Ok(()) => true,// !(^f).unsat(^a),
    Err(n) => @n < (@(^f).clauses).len() && (^f).unsat((^trail).assignments) && (@(^f).clauses)[@n].unsat((^trail).assignments),
})]
#[ensures(@f.num_vars == @(^f).num_vars)]
#[ensures(f.equisat(^f))]
fn unit_prop_current_level(f: &mut Formula, trail: &mut Trail, watches: &mut Watches, lit: Lit) -> Result<(), usize> {
    let mut j = 0;
    let watchidx = lit.to_watchidx();
    proof_assert!((@watches.watches).len() == 2 * @f.num_vars);
    proof_assert!((@watches.watches).len() > @watchidx);
    let old_trail = Ghost::record(&trail);
    let old_f = Ghost::record(&f);
    let old_w = Ghost::record(&watches);
    #[invariant(trail_inv, trail.invariant(*f))]
    #[invariant(watch_len, (@watches.watches).len() == (@(@old_w).watches).len())]
    #[invariant(watch_inv, watches.invariant(*f))]
    #[invariant(f_equi, (@old_f).equisat(*f))]
    #[invariant(f_inv, f.invariant())]
    #[invariant(dec_unch, (@trail.decisions) == (@(@old_trail).decisions))]
    #[invariant(nvars_unch, @f.num_vars == @(@old_f).num_vars)]
    #[invariant(proph_t, ^trail == ^@old_trail)]
    #[invariant(proph_f, ^f == ^@old_f)]
    #[invariant(proph_w, ^watches == ^@old_w)]
    while j < watches.watches[watchidx].len() {
        let cref = watches.watches[watchidx][j].cref;
        match unit_prop_do_outer(f, trail, watches, cref, lit, j) {
            Ok(true) => {
                j += 1;
            }
            Ok(false) => {}
            Err(cref) => {
                return Err(cref);
            }
        }
    }
    Ok(())
}

// OK on Mac
#[cfg_attr(feature = "trust_unit", trusted)]
#[maintains((mut f).invariant())]
#[maintains((mut trail).invariant(mut f))]
#[maintains((mut watches).invariant(mut f))]
#[requires(@f.num_vars < @usize::MAX/2)]
#[ensures(match result {
    Ok(()) => true, // !(^f).unsat(^a),
    Err(n) => @n < (@(^f).clauses).len() && (^f).unsat((^trail).assignments) && (@(^f).clauses)[@n].unsat((^trail).assignments),
})]
#[ensures(@f.num_vars == @(^f).num_vars)]
#[ensures(f.equisat(^f))]
pub fn unit_propagate(f: &mut Formula, trail: &mut Trail, watches: &mut Watches) -> Result<(), usize> {
    let mut i = trail.curr_i;
    let old_trail = Ghost::record(&trail);
    let old_f = Ghost::record(&f);
    let old_w = Ghost::record(&watches);
    #[invariant(f_inv, f.invariant())]
    #[invariant(trail_inv, trail.invariant(*f))]
    #[invariant(watch_len, (@watches.watches).len() == (@(@old_w).watches).len())]
    #[invariant(watch_inv, watches.invariant(*f))]
    #[invariant(f_equi, (@old_f).equisat(*f))]
    #[invariant(nvars_unch, @f.num_vars == @(@old_f).num_vars)]
    #[invariant(proph_t, ^trail == ^@old_trail)]
    #[invariant(proph_f, ^f == ^@old_f)]
    #[invariant(proph_w, ^watches == ^@old_w)]
    while i < trail.trail.len() {
        let lit = trail.trail[i].lit;
        match unit_prop_current_level(f, trail, watches, lit) {
            Ok(_) => {}
            Err(cref) => {
                return Err(cref);
            }
        }
        i += 1;
    }
    trail.curr_i = i;
    Ok(())
}
