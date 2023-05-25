use crate::{lit::*, trail::*, watches::*, clause_manager::{clause_manager::ClauseManager, common::CRef}};

#[inline]
fn unit_prop_check_rest(
    lits: &mut [Lit], trail: &Trail, watches: &mut Watches, cref: CRef, j: usize, k: usize, lit: Lit,
) -> Result<(), ()> {
    let curr_lit = lits[k];
    if !curr_lit.lit_unsat(&trail.assignments) {
        if lits[0].index() == lit.index() {
            // First
            swap(lits, k, 0);
            update_watch(lits, watches, j, 0, lit);
        } else {
            swap(lits, k, 1);
            swap(lits, 1, 0);
            update_watch(lits, watches, j, 0, lit);
            //update_watch(f, trail, watches, cref, j, 1, lit);
        }
        return Ok(()); // dont increase j
    }
    Err(())
}

#[inline(always)]
fn swap(lits: &mut [Lit], j: usize, k: usize) {
    lits.swap(j, k);
}

// The solver is included so that we can update ticks.
#[inline]
fn unit_prop_do_outer(
    clause_manager: &mut ClauseManager, trail: &mut Trail, watches: &mut Watches, cref: CRef, lit: Lit, j: usize, ticks: &mut usize,
) -> Result<bool, CRef> {
    // TODO: Move search down ? Needs to be here to avoid borrowing issues.
    let mut search = clause_manager.get_search(cref) as u32;
    let lits = clause_manager.get_clause_mut(cref);

    let other_lit = (!lit).select_other(lits[0], lits[1]);
    if other_lit.lit_sat(&trail.assignments) {
        watches[lit.to_watchidx()][j].blocker = other_lit;
        return Ok(true);
    }
    // At this point we know that none of the watched literals are sat
    let mut k = 2;
    let clause_len = lits.len() as u32;
    while k < clause_len {
        search += 1;
        if search == clause_len {
            search = 2;
        }
        match unit_prop_check_rest(lits, trail, watches, cref, j, search as usize, lit) {
            Err(_) => {}
            Ok(_) => {
                clause_manager.set_search(cref, search as u8);
                return Ok(false);
            }
        }
        k += 1;
    }
    *ticks += 1;
    if other_lit.lit_unsat(&trail.assignments) {
        return Err(cref);
    }
    if lits[0].lit_unset(&trail.assignments) {
        trail.enq_assignment(lits[0], cref);
        Ok(true)
    } else {
        trail.enq_assignment(lits[1], cref);
        lits.swap(0, 1);
        Ok(true)
    }
}

#[inline]
fn unit_prop_current_level(
    clause_manager: &mut ClauseManager, trail: &mut Trail, watches: &mut Watches, lit: Lit, ticks: &mut usize,
) -> Result<(), CRef> {
    let mut j = 0;
    let watchidx = lit.to_watchidx();
    while j < watches[watchidx].len() {
        let curr_watch = &watches[watchidx][j];
        if curr_watch.blocker.lit_sat(&trail.assignments) {
            j += 1;
        } else {
            let cref = curr_watch.cref;
            match unit_prop_do_outer(clause_manager, trail, watches, cref, lit, j, ticks) {
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

#[inline]
pub(crate) fn unit_propagate(
    clause_manager: &mut ClauseManager, trail: &mut Trail, watches: &mut Watches, ticks: &mut usize,
) -> Result<(), CRef> {
    let mut i = trail.curr_i;
    while i < trail.trail.len() {
        let lit = trail.trail[i];
        match unit_prop_current_level(clause_manager, trail, watches, lit, ticks) {
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
