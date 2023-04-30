extern crate creusot_contracts;
use creusot_contracts::{std::*, Ghost, *};

use crate::{assignments::*, clause::*, formula::*, lit::*, trail::*, util, watches::*};

#[cfg(creusot)]
use crate::logic::{logic_assignments::*, logic_formula::*};

use crate::logic::{
    logic::*,
    logic_clause::*,
    logic_trail::*, //tmp
};

#[cfg_attr(feature = "trust_unit", trusted)]
#[maintains((mut f).invariant())]
#[maintains(trail.invariant(mut f))]
#[maintains((mut watches).invariant(mut f))]
#[requires(f.num_vars@ < usize::MAX@/2)]
#[requires(lit.index_logic() < f.num_vars@)]
#[requires(!(@f.clauses@[@cref])[0].sat_inner(@trail.assignments))]
#[requires(@cref < f.clauses@.len())]
#[requires(2 <= @k && @k < (@f.clauses@[@cref]).len())]
#[requires((@(@watches.watches)[lit.to_watchidx_logic()]).len() > @j)]
#[ensures(f.num_vars@ == @(^f).num_vars)]
#[ensures(f.equisat(^f))]
#[ensures(f.clauses@.len() == (@(^f).clauses).len())]
#[ensures(!result ==> (@(@(^f).clauses)[@cref])[@k].unsat(trail.assignments) && ^f == *f && *watches == ^watches)]
#[ensures((@(@(^f).clauses)[@cref]).len() == (@f.clauses@[@cref]).len())]
fn check_and_move_watch(
    f: &mut Formula, trail: &Trail, watches: &mut Watches, cref: usize, j: usize, k: usize, lit: Lit,
) -> bool {
    let curr_lit = f[cref][k];
    if !curr_lit.lit_unsat(&trail.assignments) {
        //curr_lit.lit_unset(&trail.assignments) || curr_lit.lit_sat(&trail.assignments) {
        if f[cref][0].index() == lit.index() {
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

// TODO: Look at strategies or look at making lemmas / assertions to make it easier.
// This has previously had issues on the trail invariant and on the formula equisatisfiability.
// Solved fairly easily by Auto Level 3 when targeted direcly, but Auto Level 8/9 struggles.
#[cfg_attr(all(feature = "trust_unit", not(feature = "problem_child")), trusted)]
#[maintains((mut f).invariant())]
#[maintains((*trail).invariant(mut f))] // <-
#[maintains((*watches).invariant(mut f))]
#[requires((@f.clauses@[@cref]).len() >= 2)]
#[requires(@cref < f.clauses@.len())]
#[requires((@f.clauses@[@cref]).len() > @j)]
#[requires((@f.clauses@[@cref]).len() > @k)]
#[requires(!(@f.clauses@[@cref])[0].sat_inner(@trail.assignments))]
#[ensures(((@(@(^f).clauses)[@cref]).exchange(@f.clauses@[@cref], @j, @k)))]
#[ensures(f.num_vars@ == @(^f).num_vars)]
#[ensures(f.clauses@.len() == (@(^f).clauses).len())]
//#[ensures((@f.clauses@[@cref]).len() == (@(@(^f).clauses)[@cref]).len())]
#[ensures(f.equisat(^f))] // <-
fn swap(f: &mut Formula, trail: &Trail, watches: &Watches, cref: usize, j: usize, k: usize) {
    let old_f: Ghost<&mut Formula> = ghost! { f };

    f.clauses[cref].lits.swap(j, k);

    proof_assert!(vars_in_range_inner(@f.clauses@[@cref], f.num_vars@));
    proof_assert!(no_duplicate_indexes_inner(@f.clauses@[@cref]));

    proof_assert!(forall<a2 : Seq<AssignedState>> a2.len() == f.num_vars@ && complete_inner(a2) && (@old_f.clauses)[@cref].sat_inner(a2) ==> f.clauses@[@cref].sat_inner(a2));
    proof_assert!(eventually_sat_complete(@old_f) ==> eventually_sat_complete(@f));
    proof_assert!(^f == ^old_f.inner());
}

// This has to do f.clauses[cref] and not f[cref]
#[cfg_attr(feature = "trust_unit", trusted)]
#[maintains((mut f).invariant())]
#[maintains((trail).invariant(mut f))]
#[maintains((mut watches).invariant(mut f))]
#[requires(f.num_vars@ < usize::MAX@/2)]
#[requires(lit.to_watchidx_logic() < (@watches.watches).len())]
#[requires((@(@watches.watches)[lit.to_watchidx_logic()]).len() > @j)]
#[requires(lit.index_logic() < f.num_vars@)]
#[requires(@cref < f.clauses@.len())]
#[requires((@f.clauses@[@cref]).len() >= 2)]
#[requires(!(@f.clauses@[@cref])[0].sat_inner(@trail.assignments))]
#[ensures(!result ==> forall<m: Int> 2 <= m && m < (@f.clauses@[@cref]).len() ==> (@f.clauses@[@cref])[m].unsat(trail.assignments))]
#[ensures(!result ==> (@f.clauses@[@cref]) == (@(@(^f).clauses)[@cref]))]
#[ensures(f.num_vars@ == @(^f).num_vars)]
#[ensures(f.clauses@.len() == (@(^f).clauses).len())]
#[ensures(f.equisat(^f))]
fn exists_new_watchable_lit(
    f: &mut Formula, trail: &Trail, watches: &mut Watches, cref: usize, j: usize, lit: Lit,
) -> bool {
    let old_w: Ghost<&mut Watches> = ghost! { watches };
    let old_f: Ghost<&mut Formula> = ghost! { f };
    let clause_len: usize = f.clauses[cref].len();
    let init_search = util::max(util::min(f[cref].search, clause_len), 2); // TODO: Lame check
    let mut search = init_search;
    #[invariant(search, @search >= 2)]
    #[invariant(f_unchanged, f == *old_f)]
    #[invariant(w_unchanged, watches == *old_w)]
    #[invariant(uns, forall<m: Int> i@nit_search <= m && m < @search ==> (@f.clauses@[@cref])[m].unsat(trail.assignments))]
    // Here to help the trail invariant
    #[invariant(first_not_sat, !(@f.clauses@[@cref])[0].sat_inner(@trail.assignments))]
    while search < clause_len {
        if check_and_move_watch(f, trail, watches, cref, j, search, lit) {
            let old_f2: Ghost<&mut Formula> = ghost! { f };
            f.clauses[cref].search = search;
            proof_assert!(forall<j: Int> 0 <= j && j < f.clauses@.len() ==> @f.clauses@[j] == @(@(old_f2.inner()).clauses)[j]);
            proof_assert!(old_f2.inner().equisat(*f));
            //proof_assert!(crefs_in_range(@trail.trail, *f)); // I am here to help the trail invariant pass
            return true;
        }
        search += 1;
    }
    search = 2;
    #[invariant(search_bound, 2 <= @search && @search <= @clause_len)]
    #[invariant(f_unchanged, f == *old_f)]
    #[invariant(w_unchanged, watches == *old_w)]
    #[invariant(uns, forall<m: Int> i@nit_search <= m && m < @clause_len ==> ((@f.clauses@[@cref])[m]).unsat(trail.assignments))]
    #[invariant(uns2, forall<m: Int> 2 <= m && m < @search ==> ((@f.clauses@[@cref])[m]).unsat(trail.assignments))]
    // Here to help the trail invariant
    #[invariant(first_not_sat, !(@f.clauses@[@cref])[0].sat_inner(@trail.assignments))]
    while search < init_search {
        if check_and_move_watch(f, trail, watches, cref, j, search, lit) {
            let old_f2: Ghost<&mut Formula> = ghost! { f };
            f.clauses[cref].search = search;
            proof_assert!(forall<j: Int> 0 <= j && j < f.clauses@.len() ==> @f.clauses@[j] == @(@(old_f2.inner()).clauses)[j]);
            proof_assert!(old_f2.inner().equisat(*f));
            //proof_assert!(crefs_in_range(@trail.trail, *f)); // I am here to help the trail invariant pass
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
#[requires(f.num_vars@ < usize::MAX@/2)]
#[requires(lit.index_logic() < f.num_vars@)]
#[requires(@cref < f.clauses@.len())]
#[requires((@f.clauses@[@cref]).len() >= 2)]
#[ensures((^trail).decisions == trail.decisions)] // added
#[ensures(match result {
    Ok(true) => true,
    Ok(false) => (@(^trail).trail).len() == (@trail.trail).len(),
    Err(n) => @n < (@(^f).clauses).len() && (^f).unsat((^trail).assignments) && (@(^f).clauses)[@n].unsat((^trail).assignments),
})]
#[ensures(f.num_vars@ == @(^f).num_vars)]
#[ensures(f.equisat(^f))]
fn propagate_lit_with_regard_to_clause(
    f: &mut Formula, trail: &mut Trail, watches: &mut Watches, cref: usize, lit: Lit, j: usize,
) -> Result<bool, usize> {
    let old_w: Ghost<&mut Watches> = ghost! { watches };
    let clause = &f[cref];
    let first_lit = clause[0];
    if first_lit.lit_sat(&trail.assignments) {
        // We know blocker cannot be first, as then we would not be here
        proof_assert!(^watches == ^old_w.inner());
        proof_assert!(first_lit.index_logic() < f.num_vars@);
        watches.watches[lit.to_watchidx()][j].blocker = first_lit;
        return Ok(true);
    }
    let second_lit = clause[1];
    if second_lit.lit_sat(&trail.assignments) {
        // We know blocker cannot be second, as then we would not be here
        proof_assert!(^watches == ^old_w.inner());
        proof_assert!(second_lit.index_logic() < f.num_vars@);
        watches.watches[lit.to_watchidx()][j].blocker = second_lit;
        return Ok(true);
    }
    // At this point we know that none of the watched literals are sat
    if exists_new_watchable_lit(f, trail, watches, cref, j, lit) {
        return Ok(false); // Watches have been updated -> don't increase j
    }
    // If we have gotten here, the clause is either all false or unit
    proof_assert!(f.clauses@[@cref].unsat(trail.assignments) || ((@f.clauses@[@cref])[0]).unset(trail.assignments) || ((@f.clauses@[@cref])[1]).unset(trail.assignments));
    if first_lit.lit_unset(&trail.assignments) {
        //if f.clauses[cref].rest[0].lit_unset(&trail.assignments) {
        // zzTODOzz: Prove the runtime-check
        if second_lit.lit_unset(&trail.assignments) {
            return Ok(true);
        }
        proof_assert!(trail.invariant(*f));
        proof_assert!(!f.clauses@[@cref].unsat(trail.assignments));
        proof_assert!(f.clauses@[@cref].unit(trail.assignments));
        let step = Step {
            lit: first_lit,
            //lit: f.clauses[cref].rest[0],
            decision_level: trail.decision_level(),
            reason: Reason::Long(cref),
        };

        trail.enq_assignment(step, f);
        proof_assert!((f.clauses@[@cref]).post_unit(trail.assignments) && true);
        proof_assert!(clause_post_with_regards_to_lit((f.clauses@[@cref]), trail.assignments, first_lit));
        return Ok(true);
    } else if second_lit.lit_unset(&trail.assignments) {
        let step = Step { lit: second_lit, decision_level: trail.decision_level(), reason: Reason::Long(cref) };
        let old_c: Ghost<Clause> = ghost! { f.clauses[cref] };
        proof_assert!((@f.clauses@[@cref])[1].unset(trail.assignments));
        swap(f, trail, watches, cref, 0, 1);
        proof_assert!((@f.clauses@[@cref]).exchange(@old_c, 0, 1));
        proof_assert!((@f.clauses@[@cref])[0].unset(trail.assignments));
        trail.enq_assignment(step, f);
        proof_assert!((f.clauses@[@cref]).post_unit(trail.assignments));
        proof_assert!(clause_post_with_regards_to_lit((f.clauses@[@cref]), trail.assignments, second_lit));
        return Ok(true);
    } else {
        return Err(cref);
    }
}

#[cfg_attr(feature = "trust_unit", trusted)]
#[maintains((mut f).invariant())]
#[maintains((mut trail).invariant(mut f))]
#[maintains((mut watches).invariant(mut f))]
#[requires(f.num_vars@ < usize::MAX@/2)]
#[requires(lit.index_logic() < f.num_vars@)]
#[ensures(match result {
    Ok(()) => true,// !(^f).unsat(^a),
    Err(n) => @n < (@(^f).clauses).len() && (^f).unsat((^trail).assignments) && (@(^f).clauses)[@n].unsat((^trail).assignments),
})]
#[ensures(f.num_vars@ == @(^f).num_vars)]
#[ensures(f.equisat(^f))]
fn propagate_literal(f: &mut Formula, trail: &mut Trail, watches: &mut Watches, lit: Lit) -> Result<(), usize> {
    let mut j = 0;
    let watchidx = lit.to_watchidx();
    proof_assert!((@watches.watches).len() == 2 * f.num_vars@);
    proof_assert!((@watches.watches).len() > @watchidx);
    let old_trail: Ghost<&mut Trail> = ghost! { trail };
    let old_f: Ghost<&mut Formula> = ghost! { f };
    let old_w: Ghost<&mut Watches> = ghost! { watches };
    #[invariant(trail_inv, trail.invariant(*f))]
    #[invariant(watch_len, (@watches.watches).len() == (@old_w.watches).len())]
    #[invariant(watch_inv, watches.invariant(*f))]
    #[invariant(f_equi, old_f.equisat(*f))]
    #[invariant(f_inv, f.invariant())]
    #[invariant(dec_unch, (@trail.decisions) == (@old_trail.decisions))]
    #[invariant(nvars_unch, f.num_vars@ == @old_f.num_vars)]
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
#[requires(f.num_vars@ < usize::MAX@/2)]
#[ensures(match result {
    Ok(()) => true, // !(^f).unsat(^a),
    Err(n) => @n < (@(^f).clauses).len() && (^f).unsat((^trail).assignments) && (@(^f).clauses)[@n].unsat((^trail).assignments),
})]
#[ensures(f.num_vars@ == @(^f).num_vars)]
#[ensures(f.equisat(^f))]
pub fn unit_propagate(f: &mut Formula, trail: &mut Trail, watches: &mut Watches) -> Result<(), usize> {
    let mut i = trail.curr_i;
    let old_trail: Ghost<&mut Trail> = ghost! { trail };
    let old_f: Ghost<&mut Formula> = ghost! { f };
    let old_w: Ghost<&mut Watches> = ghost! { watches };
    #[invariant(f_inv, f.invariant())]
    #[invariant(trail_inv, trail.invariant(*f))]
    #[invariant(watch_len, (@watches.watches).len() == (@old_w.watches).len())]
    #[invariant(watch_inv, watches.invariant(*f))]
    #[invariant(f_equi, old_f.equisat(*f))]
    #[invariant(nvars_unch, f.num_vars@ == @old_f.num_vars)]
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
