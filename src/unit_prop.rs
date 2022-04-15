extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::{
    lit::*,
    clause::*,
    assignments::*,
    formula::*,
    trail::*,
    watches::*,
};

use crate::logic::{
    logic_clause::*,
    logic::*,
    logic_trail::*, //tmp
};

// OK
#[cfg_attr(all(any(trust_unit_prop, trust_all), not(untrust_all)), trusted)]
#[maintains((mut f).invariant())]
#[maintains(trail.invariant(mut f))]
#[maintains((mut watches).invariant(mut f))]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(@lit.idx < @f.num_vars)]
//#[requires((@trail.trail).len() > 0)]
#[requires(@cref < (@f.clauses).len())]
#[requires(2 <= @k && @k < (@(@f.clauses)[@cref]).len())]
#[requires((@(@f.clauses)[@cref]).len() > 2)]
#[requires((@(@watches.watches)[lit.to_watchidx_logic()]).len() > @j)]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures(f.equisat(^f))]
#[ensures((@f.clauses).len() === (@(^f).clauses).len())]
#[ensures(match result {
    Ok(_) => true, 
    Err(_) => (@(@(^f).clauses)[@cref])[@k].unsat(trail.assignments) && ^f === *f && *watches === ^watches
})]
#[ensures((@(@(^f).clauses)[@cref]).len() === (@(@f.clauses)[@cref]).len())] // ADDDED, will need proving
fn unit_prop_check_rest(f: &mut Formula, trail: &Trail, watches: &mut Watches, cref: usize, j: usize, k: usize, lit: Lit) -> Result<(), ()> {
    let curr_lit = f.clauses[cref].rest[k];
    if curr_lit.lit_unset(&trail.assignments) || curr_lit.lit_sat(&trail.assignments) { // Can swap to !unsat
        if f.clauses[cref].rest[0].idx == lit.idx { // First
            swap(f, trail, watches, cref, lit, j, k, 0);
            update_watch(f, trail, watches, cref, j, 0, lit);
        } else {
            swap(f, trail, watches, cref, lit, j, k, 1);
            update_watch(f, trail, watches, cref, j, 1, lit);
        }
        return Ok(()); // dont increase j
    }
    return Err(());
}

// OK
//#[cfg_attr(all(any(trust_unit_prop, trust_all), not(any(untrust_all, todo))), trusted)]
#[inline(always)]
#[maintains((*trail).invariant(mut f))]
#[maintains((mut f).invariant())]
#[maintains((mut watches).invariant(mut f))]
#[requires((@(@f.clauses)[@cref]).len() > @k)]
#[requires((@(@f.clauses)[@cref]).len() > @n)]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(@lit.idx < @f.num_vars)]
//#[requires((@trail.trail).len() > 0)]
#[requires(@cref < (@f.clauses).len())]
#[ensures((@(@watches.watches)[lit.to_watchidx_logic()]).len() === (@(@(^watches).watches)[lit.to_watchidx_logic()]).len())]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures((@f.clauses).len() === (@(^f).clauses).len())]
#[ensures((@(@(^f).clauses)[@cref]).len() === (@(@f.clauses)[@cref]).len())] // ADDDED, will need proving
#[ensures(f.equisat(^f))]
fn swap(f: &mut Formula, trail: &Trail, watches: &mut Watches, cref: usize, lit: Lit, j: usize, k: usize, n: usize) {
    let old_f = Ghost::record(&f);
    let second_lit = Ghost::record(&f.clauses[cref].rest[k]);
    f.clauses[cref].rest.swap(n, k);
    // Ill leave this here to clean up in later
    proof_assert!((@(@old_f).clauses).len() === (@f.clauses).len());
    proof_assert!(forall<i: Int> 0 <= i && i < (@(@old_f).clauses).len() && i != @cref ==>
        (@(@(@old_f).clauses)[i]) === (@(@f.clauses)[i]));
    proof_assert!((@(@(@old_f).clauses)[@cref]).permut((@(@f.clauses)[@cref]), 0, (@(@f.clauses)[@cref]).len()));
    proof_assert!(@(@old_f).num_vars === @f.num_vars);
    proof_assert!(lemma_swap_clause_no_dups(((@(@old_f).clauses)[@cref]), ((@f.clauses)[@cref]), 0, 1); true);
    proof_assert!(lemma_swap_maintains_post_unit(((@(@old_f).clauses)[@cref]), ((@f.clauses)[@cref]), 0, 1, trail.assignments); true);
    // Not sure if this really helps, as we are sort of "short circuiting" the j
    proof_assert!(lemma_swap_maintains_post_with_regards_to(((@(@old_f).clauses)[@cref]), ((@f.clauses)[@cref]), 0, 1, trail.assignments, @(@second_lit).idx); true);
    // Can add a lemma here to make the formula invariant faster
    proof_assert!(lemma_permut_clause_in_formula_maintains_sat(*@old_f, *f, @cref); true);
    proof_assert!(lemma_permut_clause_in_formula_maintains_unsat(*@old_f, *f, @cref); true);
    proof_assert!(^@old_f === ^f);

    // This is just the trail invariant unwrapped
    /*
    proof_assert!(trail.assignments.invariant(*f));
    proof_assert!(trail_invariant(@trail.trail, *f));
    proof_assert!(lit_to_level_invariant(@trail.lit_to_level, *f));
    proof_assert!(decisions_invariant(@trail.decisions, @trail.trail));
    proof_assert!(trail.lit_not_in_less(*f));
    proof_assert!(trail.lit_is_unique());
    proof_assert!(long_are_post_unit_inner(@trail.trail, *f, @trail.assignments));
    proof_assert!(trail.trail_entries_are_assigned());
    */
}

// Okay so the function should really be split up, now it takes too long.
// OK on Mac
#[cfg_attr(all(any(trust_unit_prop, trust_all), not(any(untrust_all, todo))), trusted)]
#[maintains((mut f).invariant())]
#[maintains((mut trail).invariant(mut f))]
#[maintains((mut watches).invariant(mut f))]
#[requires((@(@watches.watches)[lit.to_watchidx_logic()]).len() > @j)] // Added. Unsure if this is the correct way to formulate it
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(@lit.idx < @f.num_vars)]
//#[requires(0 < (@trail.trail).len() && (@trail.trail).len() < @f.num_vars)]
//#[requires(0 < (@trail.trail).len())]
//#[requires((@trail.decisions).len() > 0)] //dunno, move this to invariant?
#[requires(watches.invariant(*f))]
#[requires(@cref < (@f.clauses).len())]
#[ensures((^trail).decisions === trail.decisions)] // added
#[ensures(match result {
    Ok(true) => true, // This not generally true (@(^trail).trail).len() === 1 + (@trail.trail).len(),
    Ok(false) => (@(^trail).trail).len() === (@trail.trail).len(),
    Err(n) => @n < (@(^f).clauses).len() && (^f).unsat((^trail).assignments) && (@(^f).clauses)[@n].unsat((^trail).assignments),
})]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures(f.equisat(^f))]
fn unit_prop_do_outer(f: &mut Formula, trail: &mut Trail, watches: &mut Watches, cref: usize, lit: Lit, j: usize) -> Result<bool, usize> {
    let first_lit = f.clauses[cref].rest[0];
    if first_lit.lit_sat(&trail.assignments) {
        return Ok(true);
    }
    let second_lit = f.clauses[cref].rest[1];
    let old_f = Ghost::record(&f);
    if second_lit.lit_sat(&trail.assignments) {
        // We swap to make it faster the next time
        //swap_zero_one(f, trail, watches, cref, lit, j);
        swap(f, trail, watches, cref, lit, j, 0, 1);
        return Ok(true);
    }
    // At this point we know that none of the watched literals are sat
    let mut k: usize = 2;
    let clause_len: usize = f.clauses[cref].rest.len();
    let old_trail = Ghost::record(&trail);
    let old_w = Ghost::record(&watches);
    #[invariant(k_bound, 2 <= @k && @k <= @clause_len)]
    #[invariant(watch_len, (@watches.watches).len() === (@(@old_w).watches).len())]
    #[invariant(watch_inv, watches.invariant(*f))]
    #[invariant(trail_inv, trail.invariant(*f))]
    #[invariant(f_equi, (@old_f).equisat(*f))]
    #[invariant(f_inv, f.invariant())]
    #[invariant(f_len, (@f.clauses).len() === (@(@old_f).clauses).len())]
    #[invariant(len_same, (@(@f.clauses)[@cref]).len() === @clause_len)]
    #[invariant(nvars_unch, @f.num_vars === @(@old_f).num_vars)]
    #[invariant(f_unch, f === @old_f)] // This started failing(it is strictly speaking not needed(nvm, it is needed for the next part. Clause needs to be unchanged))
    #[invariant(w_unch, *watches === *@old_w)] // Struggling a bit with these two, but they check out after a bit
    #[invariant(dec_unch, (@trail.decisions) === (@(@old_trail).decisions))]
    //#[invariant(c_unch, ce === *@old_c)] 
    #[invariant(proph_t, ^trail === ^@old_trail)]
    #[invariant(proph_f, ^f === ^@old_f)]
    #[invariant(proph_w, ^watches === ^@old_w)]
    #[invariant(uns, forall<m: Int> 2 <= m && m < @k ==> ((@(@f.clauses)[@cref])[m]).unsat(trail.assignments))]
    while k < clause_len {
        proof_assert!((@(@watches.watches)[lit.to_watchidx_logic()]).len() > @j);
        match unit_prop_check_rest(f, trail, watches, cref, j, k, lit) {
            Err(_) => {
                proof_assert!((@old_trail).decisions === trail.decisions);
                proof_assert!(*watches === *@old_w);
                proof_assert!(*f === *@old_f);
            },
            Ok(_) => {
                return Ok(false);
            }
        }
        k += 1;
    }
    proof_assert!((@old_trail).decisions === trail.decisions);
    //proof_assert!((@(@f.clauses)[@cref])[m])
    // If we have gotten here, the clause is either all false or unit
    proof_assert!((@f.clauses)[@cref].unsat(trail.assignments) || ((@(@f.clauses)[@cref])[0]).unset(trail.assignments) || ((@(@f.clauses)[@cref])[1]).unset(trail.assignments));
    //if first_lit.lit_unset(&trail.assignments) {
    if f.clauses[cref].rest[0].lit_unset(&trail.assignments) {
        // zzTODOzz: Prove the runtime-check
        if second_lit.lit_unset(&trail.assignments) {
            return Ok(true);
        }
        //proof_assert!(trail.trail_sem_invariant(*f, *a));
        proof_assert!(trail.invariant(*f));
        proof_assert!(!(@f.clauses)[@cref].unsat(trail.assignments) && true);
        proof_assert!((@f.clauses)[@cref].unit(trail.assignments));
        //a.set_assignment(first_lit, f);
        //a.set_assignment(first_lit, f, trail); // TODO Verify preconds(might have broken loop inv)
        //proof_assert!(trail.trail_sem_invariant(*f, *a) && true);
        //trail.enq_assignment(first_lit, Reason::Long(cref), f, a);
        let step = Step {
            lit: first_lit,
            //lit: f.clauses[cref].rest[0],
            decision_level: trail.decision_level(),
            reason: Reason::Long(cref),
        };

        trail.enq_assignment(step, f);
        proof_assert!(((@f.clauses)[@cref]).post_unit(trail.assignments) && true);
        proof_assert!(clause_post_with_regards_to_lit(((@f.clauses)[@cref]), trail.assignments, first_lit));
        //proof_assert!(trail.trail_sem_invariant(*f, *a));
        return Ok(true);    
    //} else if second_lit.lit_unset(&trail.assignments) {
    } else if f.clauses[cref].rest[1].lit_unset(&trail.assignments) {
        proof_assert!(!(@f.clauses)[@cref].unsat(trail.assignments) && true && true);
        proof_assert!((@f.clauses)[@cref].unit(trail.assignments));
        //a.set_assignment(second_lit, f);
        //a.set_assignment(second_lit, f, trail); // TODO Verify preconds(might have broken loop inv)
        //trail.enq_assignment(second_lit, Reason::Long(cref), f, a);
        let step = Step {
            //lit: f.clauses[cref].rest[1],
            lit: second_lit,
            decision_level: trail.decision_level(),
            reason: Reason::Long(cref),
        };

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
        proof_assert!(lemma_swap_maintains_post_with_regards_to(((@(@old_f).clauses)[@cref]), ((@f.clauses)[@cref]), 0, 1, *a, @second_lit.idx); true);
        // Can add a lemma here to make the formula invariant faster
        proof_assert!(lemma_permut_clause_in_formula_maintains_sat(*@old_f, *f, @cref); true);
        proof_assert!(lemma_permut_clause_in_formula_maintains_unsat(*@old_f, *f, @cref); true);
        */
        return Ok(true);
    } else {
        // TODO // Do a linear pass here
        //proof_assert!((@f.clauses)[@cref].unsat(*a));
        return Err(cref);
    }
    //Ok(true)
}


// OK on Mac
#[cfg_attr(all(any(trust_unit_prop, trust_all), not(untrust_all)), trusted)]
#[maintains((mut f).invariant())]
#[maintains((mut trail).invariant(mut f))]
#[maintains((mut watches).invariant(mut f))]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(@lit.idx < @f.num_vars)]
//#[requires((@trail.trail).len() > 0)]
//#[requires((@trail.decisions).len() > 0)] //dunno, move this to invariant?
#[ensures(match result {
    Ok(()) => true,// !(^f).unsat(^a),
    Err(n) => @n < (@(^f).clauses).len() && (^f).unsat((^trail).assignments) && (@(^f).clauses)[@n].unsat((^trail).assignments),
})]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures(f.equisat(^f))]
fn unit_prop_current_level(f: &mut Formula, trail: &mut Trail, watches: &mut Watches, lit: Lit) -> Result<(), usize> {
    let mut j = 0;
    let watchidx = lit.to_watchidx();
    proof_assert!((@watches.watches).len() === 2 * @f.num_vars);
    proof_assert!((@watches.watches).len() > @watchidx);
    let old_trail = Ghost::record(&trail);
    let old_f = Ghost::record(&f);
    let old_w = Ghost::record(&watches);
    //#[invariant(trail_len, (@trail.trail).len() > 0)]
    #[invariant(trail_inv, trail.invariant(*f))]
    #[invariant(watch_len, (@watches.watches).len() === (@(@old_w).watches).len())]
    #[invariant(watch_inv, watches.invariant(*f))]
    #[invariant(f_equi, (@old_f).equisat(*f))]
    #[invariant(f_inv, f.invariant())]
    #[invariant(dec_unch, (@trail.decisions) === (@(@old_trail).decisions))]
    #[invariant(nvars_unch, @f.num_vars === @(@old_f).num_vars)]
    #[invariant(proph_t, ^trail === ^@old_trail)]
    #[invariant(proph_f, ^f === ^@old_f)]
    #[invariant(proph_w, ^watches === ^@old_w)]
    while j < watches.watches[watchidx].len() {
        let cref = watches.watches[watchidx][j].cref; // new
        match unit_prop_do_outer(f, trail, watches, cref, lit, j) {
            Ok(true) => { j += 1; },
            Ok(false) => { }, // Is this still correct?
            Err(cref) => {
                return Err(cref);
            }
        }
    }
    //proof_assert!(!f.unsat(*a)); // Only thing missing
    Ok(())
}

// OK on Mac
#[cfg_attr(all(any(trust_unit_prop, trust_all), not(untrust_all)), trusted)]
#[maintains((mut f).invariant())]
#[maintains((mut trail).invariant(mut f))]
#[maintains((mut watches).invariant(mut f))]
#[requires(@f.num_vars < @usize::MAX/2)] 
#[ensures(match result {
    Ok(()) => true, // !(^f).unsat(^a),
    Err(n) => @n < (@(^f).clauses).len() && (^f).unsat((^trail).assignments) && (@(^f).clauses)[@n].unsat((^trail).assignments),
})]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures(f.equisat(^f))]
pub fn unit_propagate(f: &mut Formula, trail: &mut Trail, watches: &mut Watches) -> Result<(), usize> {
    let mut i = trail.curr_i; 
    let old_trail = Ghost::record(&trail);
    let old_f = Ghost::record(&f);
    let old_w = Ghost::record(&watches);
    #[invariant(f_inv, f.invariant())]
    #[invariant(trail_inv, trail.invariant(*f))]
    #[invariant(watch_len, (@watches.watches).len() === (@(@old_w).watches).len())]
    #[invariant(watch_inv, watches.invariant(*f))]
    #[invariant(f_equi, (@old_f).equisat(*f))]
    #[invariant(nvars_unch, @f.num_vars === @(@old_f).num_vars)]
    #[invariant(proph_t, ^trail === ^@old_trail)]
    #[invariant(proph_f, ^f === ^@old_f)]
    #[invariant(proph_w, ^watches === ^@old_w)]
    while i < trail.trail.len() {
        let lit = trail.trail[i].lit;
        match unit_prop_current_level(f, trail, watches, lit) {
            Ok(_) => {},
            Err(cref) => {
                return Err(cref);
            }
        }
        i += 1;
    }
    trail.curr_i = i;
    //proof_assert!(!f.unsat(*a)); // Only thing missing
    Ok(())
}