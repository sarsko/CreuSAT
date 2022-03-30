extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::lit::*;
use crate::clause::*;
use crate::assignments::*;
use crate::formula::*;
use crate::trail::*;
use crate::watches::*;
use crate::logic::*;


#[trusted] // OK
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(@lit.idx < @f.num_vars)]
#[requires(trail.trail_sem_invariant(*f, *a))]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(trail.invariant(*f))]
#[requires((@trail.trail).len() > 0)]
#[requires(watches.invariant(*f))]
#[requires(@cref < (@f.clauses).len())]
#[requires(0 <= @k && @k < (@(@f.clauses)[@cref]).len())] // Changed
#[requires((@(@f.clauses)[@cref]).len() > 2)]
#[requires((@(@watches.watches)[lit.to_watchidx_logic()]).len() > 0)] 
#[requires((@(@watches.watches)[lit.to_watchidx_logic()]).len() > @j)]
#[ensures((^watches).invariant(*f))]
#[ensures(trail.trail_sem_invariant(*f, *a))]
#[ensures((*f).invariant())]
#[ensures(trail.invariant(*f))]
#[ensures(a.invariant(*f))]
fn update_watch(f: &Formula, a: &Assignments, trail: &Trail, watches: &mut Watches, cref: usize, j: usize, k: usize, lit: Lit) {
    let watchidx = lit.to_watchidx();
    let end = watches.watches[watchidx].len() - 1;
    watches.watches[watchidx].swap(j, end);
    let curr_lit = f.clauses[cref].rest[k];
    //watches.move_to_end(watchidx, j, curr_lit, f);
    match watches.watches[watchidx].pop() {
        Some(w) => {
            watches.watches[curr_lit.to_neg_watchidx()].push(w);
        },
        None => {
            panic!("Impossible");
        }
    }
}

// Takes a while, but is OK
#[trusted] // OK
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(@lit.idx < @f.num_vars)]
#[requires(trail.trail_sem_invariant(*f, *a))]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(trail.invariant(*f))]
#[requires((@trail.trail).len() > 0)]
#[requires(watches.invariant(*f))]
#[requires(@cref < (@f.clauses).len())]
#[requires(2 <= @k && @k < (@(@f.clauses)[@cref]).len())]
#[requires((@(@f.clauses)[@cref]).len() > 2)]
#[requires((@(@watches.watches)[lit.to_watchidx_logic()]).len() > 0)] // Added. Unsure if this is the correct way to formulate it
#[requires((@(@watches.watches)[lit.to_watchidx_logic()]).len() > @j)] // Added. Unsure if this is the correct way to formulate it
#[ensures((^watches).invariant(^f))]
#[ensures(trail.trail_sem_invariant(^f, *a))]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures((^f).invariant())]
#[ensures(trail.invariant(^f))]
#[ensures(a.invariant(^f))]
#[ensures(f.equisat(^f))]
#[ensures((@f.clauses).len() === (@(^f).clauses).len())]
#[ensures(match result {
    Ok(_) => true, // not correct -> //(@(@(^f).clauses)[@cref])[@k].sat(*a)  || (@(@(^f).clauses)[@cref])[@k].unset(*a)
    Err(_) => (@(@(^f).clauses)[@cref])[@k].unsat(*a) && ^f === *f && *watches === ^watches
})]
fn unit_prop_check_rest(f: &mut Formula, a: &Assignments, trail: &Trail, watches: &mut Watches, cref: usize, j: usize, k: usize, lit: Lit) -> Result<(), ()> {
    let curr_lit = f.clauses[cref].rest[k];
    if curr_lit.lit_unset(a) || curr_lit.lit_sat(a) { // Can swap to !unsat
        let old_f = Ghost::record(&f);
        if f.clauses[cref].rest[0].idx == lit.idx { // First
            f.clauses[cref].rest.swap(0,k);
            proof_assert!((@(@old_f).clauses).len() === (@f.clauses).len());
            proof_assert!(forall<i: Int> 0 <= i && i < (@(@old_f).clauses).len() && i != @cref ==>
                (@(@(@old_f).clauses)[i]) === (@(@f.clauses)[i]));
            proof_assert!((@(@(@old_f).clauses)[@cref]).permut((@(@f.clauses)[@cref]), 0, (@(@f.clauses)[@cref]).len()));
            proof_assert!(@(@old_f).num_vars === @f.num_vars);
            proof_assert!(lemma_swap_clause_no_dups(((@(@old_f).clauses)[@cref]), ((@f.clauses)[@cref]), 0, 1); true);
            proof_assert!(lemma_swap_maintains_post_unit(((@(@old_f).clauses)[@cref]), ((@f.clauses)[@cref]), 0, 1, *a); true);
            // Not sure if this really helps, as we are sort of "short circuiting" the j
            proof_assert!(lemma_swap_maintains_post_with_regards_to(((@(@old_f).clauses)[@cref]), ((@f.clauses)[@cref]), 0, 1, *a, @(@(@f.clauses)[@cref])[0].idx); true);
            // Can add a lemma here to make the formula invariant faster
            proof_assert!(lemma_permut_clause_in_formula_maintains_sat(*@old_f, *f, @cref); true);
            proof_assert!(lemma_permut_clause_in_formula_maintains_unsat(*@old_f, *f, @cref); true);
            proof_assert!(^@old_f === ^f);
            /*
            f.clauses[cref].rest[0] = curr_lit;
            f.clauses[cref].rest[k] = first_lit;
            */
            update_watch(f, a, trail, watches, cref, j, 0, lit);
        } else {
            f.clauses[cref].rest.swap(1,k);
            proof_assert!((@(@old_f).clauses).len() === (@f.clauses).len());
            proof_assert!(forall<i: Int> 0 <= i && i < (@(@old_f).clauses).len() && i != @cref ==>
                (@(@(@old_f).clauses)[i]) === (@(@f.clauses)[i]));
            proof_assert!((@(@(@old_f).clauses)[@cref]).permut((@(@f.clauses)[@cref]), 0, (@(@f.clauses)[@cref]).len()));
            proof_assert!(@(@old_f).num_vars === @f.num_vars);
            proof_assert!(lemma_swap_clause_no_dups(((@(@old_f).clauses)[@cref]), ((@f.clauses)[@cref]), 0, 1); true);
            proof_assert!(lemma_swap_maintains_post_unit(((@(@old_f).clauses)[@cref]), ((@f.clauses)[@cref]), 0, 1, *a); true);
            // Not sure if this really helps, as we are sort of "short circuiting" the j
            proof_assert!(lemma_swap_maintains_post_with_regards_to(((@(@old_f).clauses)[@cref]), ((@f.clauses)[@cref]), 0, 1, *a, @(@(@f.clauses)[@cref])[1].idx); true);
            // Can add a lemma here to make the formula invariant faster
            proof_assert!(lemma_permut_clause_in_formula_maintains_sat(*@old_f, *f, @cref); true);
            proof_assert!(lemma_permut_clause_in_formula_maintains_unsat(*@old_f, *f, @cref); true);
            proof_assert!(^@old_f === ^f);
            // We dont NEED the second swap
            // May be marginally faster to swap. Check back later
            //f.clauses[cref].rest.swap(0,1);
            //f.clauses[cref].rest[0] = curr_lit;
            //f.clauses[cref].rest[k] = second_lit;
            //f.clauses[cref].rest[1] = first_lit;
            update_watch(f, a, trail, watches, cref, j, 1, lit);
        }
        /*
        let watchidx = lit.to_watchidx();
        let end = watches.watches[watchidx].len() - 1;
        watches.watches[watchidx].swap(j, end);
        match watches.watches[watchidx].pop() {
            Some(w) => {
                watches.watches[curr_lit.to_neg_watchidx()].push(w);
            },
            None => {
                unreachable!();
            }
        }
        */
        return Ok(()); // dont increase j
    }
    return Err(());
}

// Swaps first and second
#[trusted] // OK
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(@lit.idx < @f.num_vars)]
#[requires(trail.trail_sem_invariant(*f, *a))]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(trail.invariant(*f))]
#[requires((@trail.trail).len() > 0)]
#[requires(watches.invariant(*f))]
#[requires(@cref < (@f.clauses).len())]
#[ensures((^watches).invariant(^f))]
#[ensures(trail.trail_sem_invariant(^f, *a))]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures((^f).invariant())]
#[ensures((*trail).invariant(^f))]
#[ensures((*a).invariant(^f))]
#[ensures(f.equisat(^f))]
fn swap(f: &mut Formula, a: &Assignments, trail: &Trail, watches: &mut Watches, cref: usize, lit: Lit, j: usize) {
    let old_f = Ghost::record(&f);
    let second_lit = f.clauses[cref].rest[1];
    f.clauses[cref].rest.swap(0,1);
    // These are not equivalent to swapping somehow (:
    //f.clauses[cref].rest[0] = second_lit;
    //f.clauses[cref].rest[1] = first_lit;
    proof_assert!((@(@old_f).clauses).len() === (@f.clauses).len());
    proof_assert!(forall<i: Int> 0 <= i && i < (@(@old_f).clauses).len() && i != @cref ==>
        (@(@(@old_f).clauses)[i]) === (@(@f.clauses)[i]));
    proof_assert!((@(@(@old_f).clauses)[@cref]).permut((@(@f.clauses)[@cref]), 0, (@(@f.clauses)[@cref]).len()));
    proof_assert!(@(@old_f).num_vars === @f.num_vars);
    proof_assert!(lemma_swap_clause_no_dups(((@(@old_f).clauses)[@cref]), ((@f.clauses)[@cref]), 0, 1); true);
    proof_assert!(lemma_swap_maintains_post_unit(((@(@old_f).clauses)[@cref]), ((@f.clauses)[@cref]), 0, 1, *a); true);
    // Not sure if this really helps, as we are sort of "short circuiting" the j
    proof_assert!(lemma_swap_maintains_post_with_regards_to(((@(@old_f).clauses)[@cref]), ((@f.clauses)[@cref]), 0, 1, *a, @second_lit.idx); true);
    // Can add a lemma here to make the formula invariant faster
    proof_assert!(lemma_permut_clause_in_formula_maintains_sat(*@old_f, *f, @cref); true);
    proof_assert!(lemma_permut_clause_in_formula_maintains_unsat(*@old_f, *f, @cref); true);
    proof_assert!(^@old_f === ^f);
}


//#[trusted] // Some work to do
#[requires((@(@watches.watches)[lit.to_watchidx_logic()]).len() > @j)] // Added. Unsure if this is the correct way to formulate it
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(@lit.idx < @f.num_vars)]
#[requires(trail.trail_sem_invariant(*f, *a))]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(trail.invariant(*f))]
#[requires((@trail.trail).len() > 0)]
#[requires(watches.invariant(*f))]
#[requires(@cref < (@f.clauses).len())]
#[ensures((^watches).invariant(^f))]
#[ensures((^trail).trail_sem_invariant(^f, ^a))]
#[ensures((@(^trail).trail).len() === (@trail.trail).len())]
/*
#[ensures(match result {
    Ok(true) => !(^f).unsat(^a),
    Ok(false) => !(^f).unsat(^a),
    Err(n) => @n < (@(^f).clauses).len() && (^f).unsat(^a) && (@(^f).clauses)[@n].unsat(^a),
})]
*/
#[ensures((*a).compatible(^a))]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures((^f).invariant())]
#[ensures((^trail).invariant(^f))]
#[ensures((^a).invariant(^f))]
#[ensures(f.equisat(^f))]
fn unit_prop_do_outer(f: &mut Formula, a: &mut Assignments, trail: &mut Trail, watches: &mut Watches, cref: usize, lit: Lit, j: usize) -> Result<bool, usize> {
    let first_lit = f.clauses[cref].rest[0];
    if first_lit.lit_sat(&a) {
        return Ok(true);
    }
    let second_lit = f.clauses[cref].rest[1];
    let old_f = Ghost::record(&f);
    if second_lit.lit_sat(&a) {
        // We swap to make it faster the next time
        swap(f, a, trail, watches, cref, lit, j);
        return Ok(true);
    }
    // At this point we know that none of the watched literals are sat
    let mut k: usize = 2;
    let clause_len: usize = f.clauses[cref].rest.len();
    let old_trail = Ghost::record(&trail);
    let old_a = Ghost::record(&a);
    let old_w = Ghost::record(&watches);
    #[invariant(k_bound, 2 <= @k && @k <= @clause_len)]
    #[invariant(watch_len, (@watches.watches).len() === (@(@old_w).watches).len())]
    #[invariant(watch_inv, watches.invariant(*f))]
    #[invariant(trail_sem, trail.trail_sem_invariant(*f, *a))]
    /*
    #[invariant(f_equi, (@old_f).equisat(*f))]
    #[invariant(f_inv, f.invariant())]
    #[invariant(f_len, (@f.clauses).len() === (@(@old_f).clauses).len())]
    */
    #[invariant(f_unch, f === @old_f)]
    #[invariant(ass_inv, a.invariant(*f))]
    #[invariant(a_compat, (@old_a).compatible(*a))]
    #[invariant(nvars_unch, @f.num_vars === @(@old_f).num_vars)]
    #[invariant(w_unch, watches === @old_w)]
    #[invariant(proph_t, ^trail === ^@old_trail)]
    #[invariant(proph_f, ^f === ^@old_f)]
    #[invariant(proph_a, ^a === ^@old_a)]
    #[invariant(proph_w, ^watches === ^@old_w)]
    #[invariant(uns, forall<m: Int> 2 <= m && m < @k ==> ((@(@f.clauses)[@cref])[m]).unsat(*a))]
    while k < clause_len {
        //proof_assert!((@(@watches.watches)[lit.to_watchidx_logic()]).len() > @j);
        match unit_prop_check_rest(f, a, trail, watches, cref, j, k, lit) {
            Err(_) => {},
            Ok(_) => {
                return Ok(false);
            }
        }
        k += 1;
    }
    //proof_assert!((@(@f.clauses)[@cref])[m])
    // Ok so the assertions except the unsat or unit(which doesnt assert) are just really slow
    // If we have gotten here, the clause is either all false or unit
    proof_assert!((@f.clauses)[@cref].unsat(*a) || ((@f.clauses)[@cref].unit(*a)));
    if first_lit.lit_unset(a) {
    //if f.clauses[cref].rest[0].lit_unset(a) {
        // Could add a runtime check here, which could simplify the proof.
        proof_assert!(trail.trail_sem_invariant(*f, *a));
        proof_assert!(!(@f.clauses)[@cref].unsat(*a) && true);
        proof_assert!((@f.clauses)[@cref].unit(*a));
        a.set_assignment(first_lit, f);
        proof_assert!(trail.trail_sem_invariant(*f, *a) && true);
        proof_assert!(((@f.clauses)[@cref]).post_unit(*a) && true);
        proof_assert!(clause_post_with_regards_to_lit(((@f.clauses)[@cref]), *a, first_lit));
        trail.enq_assignment(first_lit, Reason::Long(cref), f, a);
        return Ok(true);
    //} else if f.clauses[cref].rest[1].lit_unset(a) {
        proof_assert!(trail.trail_sem_invariant(*f, *a));
    } else if second_lit.lit_unset(a) {
        proof_assert!(!(@f.clauses)[@cref].unsat(*a) && true && true);
        proof_assert!((@f.clauses)[@cref].unit(*a));
        a.set_assignment(second_lit, f);
        proof_assert!(trail.trail_sem_invariant(*f, *a) && true);
        proof_assert!(((@f.clauses)[@cref]).post_unit(*a));
        proof_assert!(clause_post_with_regards_to_lit(((@f.clauses)[@cref]), *a, second_lit));
        trail.enq_assignment(second_lit, Reason::Long(cref), f, a);
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

        // TODO
        proof_assert!((@f.clauses)[@cref].unsat(*a));
        return Err(cref);
    }
    //return Ok(true);
}


#[trusted] // Also lacking the post for OK
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(@lit.idx < @f.num_vars)]
#[requires(trail.trail_sem_invariant(*f, *a))]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(trail.invariant(*f))]
#[requires((@trail.trail).len() > 0)]
#[requires(watches.invariant(*f))]
#[ensures((^watches).invariant(^f))]
#[ensures((^trail).trail_sem_invariant(^f, ^a))]
#[ensures((@(^trail).trail).len() === (@trail.trail).len())]
#[ensures(match result {
    Ok(()) => !(^f).unsat(^a),
    Err(n) => @n < (@(^f).clauses).len() && (^f).unsat(^a) && (@(^f).clauses)[@n].unsat(^a),
})]
#[ensures((*a).compatible(^a))]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures((^f).invariant())]
#[ensures((^trail).invariant(^f))]
#[ensures((^a).invariant(^f))]
#[ensures(f.equisat_compatible(^f))]
fn unit_prop_current_level(f: &mut Formula, a: &mut Assignments, trail: &mut Trail, watches: &mut Watches, lit: Lit) -> Result<(), usize> {
    let mut j = 0;
    let watchidx = lit.to_watchidx();
    proof_assert!((@watches.watches).len() === 2 * @f.num_vars);
    proof_assert!((@watches.watches).len() > @watchidx);
    let old_trail = Ghost::record(&trail);
    let old_f = Ghost::record(&f);
    let old_a = Ghost::record(&a);
    let old_w = Ghost::record(&watches);
    #[invariant(trail_sem, trail.trail_sem_invariant(*f, *a))]
    #[invariant(trail_inv, trail.invariant(*f))]
    #[invariant(trail_len, (@trail.trail).len() === (@(@old_trail).trail).len())]
    #[invariant(watch_len, (@watches.watches).len() === (@(@old_w).watches).len())]
    #[invariant(watch_inv, watches.invariant(*f))]
    #[invariant(f_equi, (@old_f).equisat(*f))]
    #[invariant(f_inv, f.invariant())]
    #[invariant(ass_inv, a.invariant(*f))]
    #[invariant(a_compat, (@old_a).compatible(*a))]
    #[invariant(nvars_unch, @f.num_vars === @(@old_f).num_vars)]
    #[invariant(proph_t, ^trail === ^@old_trail)]
    #[invariant(proph_f, ^f === ^@old_f)]
    #[invariant(proph_a, ^a === ^@old_a)]
    #[invariant(proph_w, ^watches === ^@old_w)]
    while j < watches.watches[watchidx].len() {
        let cref = watches.watches[watchidx][j].cref; // new
        match unit_prop_do_outer(f, a, trail, watches, cref, lit, j) {
            Ok(true) => { j += 1; },
            Ok(false) => {},
            Err(cref) => {
                return Err(cref);
            }
        }
    }
    proof_assert!(!f.unsat(*a)); // Only thing missing
    Ok(())
}

// Gotta add some pres in solver_dpll
#[trusted] // Lacking the post for OK
#[requires(@f.num_vars < @usize::MAX/2)] // TODO
#[requires(trail.trail_sem_invariant(*f, *a))]
#[ensures((^trail).trail_sem_invariant(^f, ^a))]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(trail.invariant(*f))]
#[requires((@trail.trail).len() > 0)]
#[requires(watches.invariant(*f))]
#[ensures((^watches).invariant(^f))]
#[ensures((@(^trail).trail).len() === (@trail.trail).len())]
#[ensures(match result {
    Ok(()) => !(^f).unsat(^a),
    Err(n) => @n < (@(^f).clauses).len() && (^f).unsat(^a) && (@(^f).clauses)[@n].unsat(^a),
})]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures((^f).invariant())]
#[ensures((^trail).invariant(^f))]
#[ensures((^a).invariant(^f))]
#[ensures(f.equisat_compatible(^f))]
pub fn unit_propagate_WIP(f: &mut Formula, a: &mut Assignments, trail: &mut Trail, watches: &mut Watches) -> Result<(), usize> {
    let mut i = 0;
    let d = trail.trail.len() - 1;
    let old_trail = Ghost::record(&trail);
    let old_f = Ghost::record(&f);
    let old_a = Ghost::record(&a);
    let old_w = Ghost::record(&watches);
    #[invariant(trail_sem, trail.trail_sem_invariant(*f, *a))]
    #[invariant(trail_inv, trail.invariant(*f))]
    #[invariant(trail_len, (@trail.trail).len() === (@(@old_trail).trail).len())]
    #[invariant(watch_len, (@watches.watches).len() === (@(@old_w).watches).len())]
    #[invariant(watch_inv, watches.invariant(*f))]
    #[invariant(f_equi, (@old_f).equisat_compatible(*f))]
    #[invariant(f_inv, f.invariant())]
    #[invariant(ass_inv, a.invariant(*f))]
    #[invariant(a_compat, (@old_a).compatible(*a))]
    #[invariant(nvars_unch, @f.num_vars === @(@old_f).num_vars)]
    #[invariant(proph_t, ^trail === ^@old_trail)]
    #[invariant(proph_f, ^f === ^@old_f)]
    #[invariant(proph_a, ^a === ^@old_a)]
    #[invariant(proph_w, ^watches === ^@old_w)]
    while i < trail.trail[d].len() {
        let lit = trail.trail[d][i];
        match unit_prop_current_level(f, a, trail, watches, lit) {
            Ok(_) => {},
            Err(cref) => {
                return Err(cref);
            }
        }
        i += 1;
    }
    proof_assert!(!f.unsat(*a)); // Only thing missing
    Ok(())
}