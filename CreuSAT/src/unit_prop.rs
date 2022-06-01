// Just swap missing (15.04, 16:31)
extern crate creusot_contracts;
use creusot_contracts::logic::Ghost;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{formula::*, lit::*, trail::*, watches::*};

use crate::logic::{
    logic::*,
    logic_clause::*,
    logic_trail::*, //tmp
};

#[cfg_attr(feature = "trust_unit", trusted)]
#[maintains((mut f).invariant())]
#[maintains(trail.invariant(mut f))]
#[maintains((mut watches).invariant(mut f))]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(lit.index_logic() < @f.num_vars)]
//#[requires((@trail.trail).len() > 0)]
#[requires(!(@(@f.clauses)[@cref])[0].sat_inner(@trail.assignments))]
#[requires(@cref < (@f.clauses).len())]
#[requires(2 <= @k && @k < (@(@f.clauses)[@cref]).len())]
#[requires((@(@f.clauses)[@cref]).len() > 2)]
#[requires((@(@watches.watches)[lit.to_watchidx_logic()]).len() > @j)]
#[ensures(@f.num_vars == @(^f).num_vars)]
#[ensures(f.equisat(^f))]
#[ensures((@f.clauses).len() == (@(^f).clauses).len())]
#[ensures(!result ==> (@(@(^f).clauses)[@cref])[@k].unsat(trail.assignments) && ^f == *f && *watches == ^watches)]
#[ensures((@(@(^f).clauses)[@cref]).len() == (@(@f.clauses)[@cref]).len())]
fn check_and_move_watch(
    f: &mut Formula, trail: &Trail, watches: &mut Watches, cref: usize, j: usize, k: usize, lit: Lit,
) -> bool {
    let curr_lit = f.clauses[cref].rest[k];
    if !curr_lit.lit_unsat(&trail.assignments) {
        //curr_lit.lit_unset(&trail.assignments) || curr_lit.lit_sat(&trail.assignments) {
        if f.clauses[cref].rest[0].index() == lit.index() {
            // First
            swap(f, trail, watches, cref, k, 0);
            update_watch(f, trail, watches, cref, j, 0, lit);
        } else {
            swap(f, trail, watches, cref, k, 1);
            swap(f, trail, watches, cref, 1, 0);
            //update_watch(f, trail, watches, cref, j, 1, lit);
            update_watch(f, trail, watches, cref, j, 0, lit);
        }
        return true; // dont increase j
    }
    return false;
}

#[cfg_attr(feature = "trust_unit", trusted)]
#[maintains((mut f).invariant())]
#[maintains((*trail).invariant(mut f))]
#[maintains((*watches).invariant(mut f))]
#[requires((@(@f.clauses)[@cref]).len() >= 2)]
#[requires(@cref < (@f.clauses).len())]
#[requires((@(@f.clauses)[@cref]).len() > @j)]
#[requires((@(@f.clauses)[@cref]).len() > @k)]
#[requires(!(@(@f.clauses)[@cref])[0].sat_inner(@trail.assignments))]
//#[requires(@f.num_vars < @usize::MAX/2)]
#[ensures(((@(@(^f).clauses)[@cref]).exchange(@(@f.clauses)[@cref], @j, @k)))]
#[ensures(@f.num_vars == @(^f).num_vars)]
#[ensures((@f.clauses).len() == (@(^f).clauses).len())]
//#[ensures((@(@f.clauses)[@cref]).len() == (@(@(^f).clauses)[@cref]).len())]
#[ensures(f.equisat(^f))]
fn swap(f: &mut Formula, trail: &Trail, watches: &Watches, cref: usize, j: usize, k: usize) {
    let old_f = ghost! { f };
    proof_assert!(no_duplicate_indexes_inner(@(@f.clauses)[@cref]));
    proof_assert!(long_are_post_unit_inner(@trail.trail, *f, @trail.assignments) && true);
    f.clauses[cref].rest.swap(j, k);
    proof_assert!((@(@f.clauses)[@cref]).exchange(@(@(old_f.inner()).clauses)[@cref], @j, @k));
    proof_assert!(forall<i: Int> 0 <= i && i < (@trail.trail).len() ==>
    match (@trail.trail)[i].reason {
    Reason::Long(cref2) => { @cref != @cref2 },
        _ => true,
    });
    proof_assert!(vars_in_range_inner(@(@f.clauses)[@cref], @f.num_vars));
    proof_assert!(no_duplicate_indexes_inner(@(@f.clauses)[@cref]));
    proof_assert!(long_are_post_unit_inner(@trail.trail, *f, @trail.assignments));
    proof_assert!(^old_f.inner() == ^f);
    proof_assert!(lit_not_in_less_inner(@trail.trail, *f));
    proof_assert!(crefs_in_range(@trail.trail, *f));
}

//#[cfg_attr(feature = "trust_unit", trusted)]
#[requires(@(@f.clauses)[@cref].search >= 2 && @(@f.clauses)[@cref].search <= (@(@f.clauses)[@cref]).len())]
#[ensures(@(@(^f).clauses)[@cref].search >= 2 && @(@(^f).clauses)[@cref].search <= (@(@(^f).clauses)[@cref]).len())]
#[maintains((mut f).invariant())]
#[maintains((trail).invariant(mut f))]
#[maintains((mut watches).invariant(mut f))]
#[requires(lit.to_watchidx_logic() < (@watches.watches).len())]
#[requires((@(@watches.watches)[lit.to_watchidx_logic()]).len() > @j)]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(lit.index_logic() < @f.num_vars)]
#[requires(watches.invariant(*f))]
#[requires(@cref < (@f.clauses).len())]
#[requires((@(@f.clauses)[@cref]).len() >= 2)]
#[requires(!(@(@f.clauses)[@cref])[0].sat_inner(@trail.assignments))]
#[ensures(!result ==> forall<m: Int> 2 <= m && m < (@(@f.clauses)[@cref]).len() ==> (@(@f.clauses)[@cref])[m].unsat(trail.assignments))]
#[ensures(!result ==> (@(@f.clauses)[@cref]) == (@(@(^f).clauses)[@cref]))]
#[ensures(@f.num_vars == @(^f).num_vars)]
#[ensures((@f.clauses).len() == (@(^f).clauses).len())]
#[ensures(f.equisat(^f))]
fn exists_new_watchable_lit(
    f: &mut Formula, trail: &Trail, watches: &mut Watches, cref: usize, j: usize, lit: Lit,
) -> bool {
    let old_w = ghost! { watches };
    let old_f = ghost! { f };
    let mut search = f.clauses[cref].search;
    let init_search = f.clauses[cref].search; //search;
    let clause_len: usize = f.clauses[cref].rest.len();
    #[invariant(search, @(@f.clauses)[@cref].search >= @init_search && @search <= @clause_len)]
    #[invariant(uns, forall<m: Int> @init_search <= m && m < @search ==> ((@(@f.clauses)[@cref])[m]).unsat(trail.assignments))]
    #[invariant(first_not_sat, !(@(@f.clauses)[@cref])[0].sat_inner(@trail.assignments))]
    #[invariant(search_bound, 2 <= @search && @search <= @clause_len)]
    #[invariant(equi, old_f.inner().equisat(*f))]
    #[invariant(f_unchanged, f == old_f.inner())]
    #[invariant(w_unchanged, *watches == *old_w.inner())]
    #[invariant(proph_f, ^f == ^old_f.inner())]
    #[invariant(proph_w, ^watches == ^old_w.inner())]
    while search < clause_len {
        if check_and_move_watch(f, trail, watches, cref, j, search, lit) {
            proof_assert!(old_f.inner().equisat(*f)); // TODO on proving setting search
            let old_f2 = ghost! { f };
            f.clauses[cref].search = search;
            proof_assert!(forall<j: Int> 0 <= j && j < (@f.clauses).len() ==> @(@f.clauses)[j] == @(@(old_f2.inner()).clauses)[j]);
            proof_assert!(old_f2.inner().equisat(*f)); // TODO on proving setting search
            return true;
        }
        search += 1;
    }
    search = 2;
    #[invariant(search, @(@f.clauses)[@cref].search >= @init_search && @search <= @clause_len)]
    #[invariant(uns, forall<m: Int> @init_search <= m && m < @clause_len ==> ((@(@f.clauses)[@cref])[m]).unsat(trail.assignments))]
    #[invariant(uns2, forall<m: Int> 2 <= m && m < @search ==> ((@(@f.clauses)[@cref])[m]).unsat(trail.assignments))]
    #[invariant(first_not_sat, !(@(@f.clauses)[@cref])[0].sat_inner(@trail.assignments))]
    #[invariant(search_bound, 2 <= @search && @search <= @clause_len)]
    #[invariant(equi, old_f.inner().equisat(*f))]
    #[invariant(f_unchanged, f == old_f.inner())]
    #[invariant(w_unchanged, *watches == *old_w.inner())]
    #[invariant(proph_f, ^f == ^old_f.inner())]
    #[invariant(proph_w, ^watches == ^old_w.inner())]
    while search < init_search {
        if check_and_move_watch(f, trail, watches, cref, j, search, lit) {
            proof_assert!(old_f.inner().equisat(*f));
            let old_f2 = ghost! { f };
            f.clauses[cref].search = search;
            proof_assert!(forall<j: Int> 0 <= j && j < (@f.clauses).len() ==> @(@f.clauses)[j] == @(@(old_f2.inner()).clauses)[j]);
            proof_assert!(old_f2.inner().equisat(*f));
            return true;
        }
        search += 1;
    }
    false
}

#[cfg_attr(feature = "trust_unit", trusted)]
#[maintains((mut f).invariant())]
#[maintains((mut trail).invariant(mut f))]
#[maintains((mut watches).invariant(mut f))]
#[requires(lit.to_watchidx_logic() < (@watches.watches).len())]
#[requires((@(@watches.watches)[lit.to_watchidx_logic()]).len() > @j)]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires(lit.index_logic() < @f.num_vars)]
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
fn propagate_lit_with_regard_to_clause(
    f: &mut Formula, trail: &mut Trail, watches: &mut Watches, cref: usize, lit: Lit, j: usize,
) -> Result<bool, usize> {
    let old_w = ghost! { watches };
    let clause = &f.clauses[cref];
    let first_lit = clause.rest[0];
    if first_lit.lit_sat(&trail.assignments) {
        // We know blocker cannot be first, as then we would not be here
        proof_assert!(^watches == ^old_w.inner());
        proof_assert!(first_lit.index_logic() < @f.num_vars);
        watches.watches[lit.to_watchidx()][j].blocker = first_lit;
        return Ok(true);
    }
    let second_lit = clause.rest[1];
    if second_lit.lit_sat(&trail.assignments) {
        // We swap to make it faster the next time
        //swap_zero_one(f, trail, watches, cref, lit, j);
        //swap(f, trail, watches, cref, 0, 1);
        // We know blocker cannot be second, as then we would not be here
        proof_assert!(^watches == ^old_w.inner());
        proof_assert!(second_lit.index_logic() < @f.num_vars);
        watches.watches[lit.to_watchidx()][j].blocker = second_lit;
        return Ok(true);
    }
    // At this point we know that none of the watched literals are sat
    if exists_new_watchable_lit(f, trail, watches, cref, j, lit) {
        return Ok(false); // Watches have been updated -> don't increase j
    }
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
        let step = Step { lit: second_lit, decision_level: trail.decision_level(), reason: Reason::Long(cref) };
        let old_c = ghost! { f.clauses[cref] };
        proof_assert!((@(@f.clauses)[@cref])[1].unset(trail.assignments));
        swap(f, trail, watches, cref, 0, 1);
        proof_assert!((@(@f.clauses)[@cref]).exchange(@old_c.inner(), 0, 1));
        proof_assert!((@(@f.clauses)[@cref])[0].unset(trail.assignments));
        trail.enq_assignment(step, f);
        proof_assert!(((@f.clauses)[@cref]).post_unit(trail.assignments));
        proof_assert!(clause_post_with_regards_to_lit(((@f.clauses)[@cref]), trail.assignments, second_lit));
        return Ok(true);
    } else {
        return Err(cref);
    }
}

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
fn propagate_literal(f: &mut Formula, trail: &mut Trail, watches: &mut Watches, lit: Lit) -> Result<(), usize> {
    let mut j = 0;
    let watchidx = lit.to_watchidx();
    proof_assert!((@watches.watches).len() == 2 * @f.num_vars);
    proof_assert!((@watches.watches).len() > @watchidx);
    let old_trail = ghost! { trail };
    let old_f = ghost! { f };
    let old_w = ghost! { watches };
    #[invariant(trail_inv, trail.invariant(*f))]
    #[invariant(watch_len, (@watches.watches).len() == (@(old_w.inner()).watches).len())]
    #[invariant(watch_inv, watches.invariant(*f))]
    #[invariant(f_equi, (old_f.inner()).equisat(*f))]
    #[invariant(f_inv, f.invariant())]
    #[invariant(dec_unch, (@trail.decisions) == (@(old_trail.inner()).decisions))]
    #[invariant(nvars_unch, @f.num_vars == @(old_f.inner()).num_vars)]
    #[invariant(proph_t, ^trail == ^old_trail.inner())]
    #[invariant(proph_f, ^f == ^old_f.inner())]
    #[invariant(proph_w, ^watches == ^old_w.inner())]
    while j < watches.watches[watchidx].len() {
        let curr_watch = &watches.watches[watchidx][j];
        if curr_watch.blocker.lit_sat(&trail.assignments) {
            j += 1;
        } else {
            let cref = curr_watch.cref;
            match propagate_lit_with_regard_to_clause(f, trail, watches, cref, lit, j) {
                Ok(true) => {
                    j += 1;
                }
                Ok(false) => {}
                Err(cref) => {
                    return Err(cref);
                }
            }
        }
    }
    Ok(())
}

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
    let old_trail = ghost! { trail };
    let old_f = ghost! { f };
    let old_w = ghost! { watches };
    #[invariant(f_inv, f.invariant())]
    #[invariant(trail_inv, trail.invariant(*f))]
    #[invariant(watch_len, (@watches.watches).len() == (@(old_w.inner()).watches).len())]
    #[invariant(watch_inv, watches.invariant(*f))]
    #[invariant(f_equi, (old_f.inner()).equisat(*f))]
    #[invariant(nvars_unch, @f.num_vars == @(old_f.inner()).num_vars)]
    #[invariant(proph_t, ^trail == ^old_trail.inner())]
    #[invariant(proph_f, ^f == ^old_f.inner())]
    #[invariant(proph_w, ^watches == ^old_w.inner())]
    while i < trail.trail.len() {
        let lit = trail.trail[i].lit;
        match propagate_literal(f, trail, watches, lit) {
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
