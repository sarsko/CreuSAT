use crate::{formula::*, lit::*, trail::*, watches::*};

#[inline]
fn unit_prop_check_rest(
    f: &mut Formula, trail: &Trail, watches: &mut Watches, cref: usize, j: usize, k: usize, lit: Lit,
) -> Result<(), ()> {
    let curr_lit = f[cref][k];
    if !curr_lit.lit_unsat(&trail.assignments) {
        if f[cref][0].index() == lit.index() {
            // First
            swap(f, trail, watches, cref, k, 0);
            update_watch(f, watches, cref, j, 0, lit);
        } else {
            swap(f, trail, watches, cref, k, 1);
            swap(f, trail, watches, cref, 1, 0);
            update_watch(f, watches, cref, j, 0, lit);
            //update_watch(f, trail, watches, cref, j, 1, lit);
        }
        return Ok(()); // dont increase j
    }
    Err(())
}

#[inline(always)]
fn swap(f: &mut Formula, _trail: &Trail, _watches: &Watches, cref: usize, j: usize, k: usize) {
    f[cref].swap(j, k);
}

// The solver is included so that we can update ticks.
#[inline]
fn unit_prop_do_outer(
    formula: &mut Formula, trail: &mut Trail, watches: &mut Watches, cref: usize, lit: Lit, j: usize, ticks: &mut usize,
) -> Result<bool, usize> {
    let clause = &formula[cref];

    let other_lit = (!lit).select_other(clause[0], clause[1]);
    if other_lit.lit_sat(&trail.assignments) {
        watches[lit.to_watchidx()][j].blocker = other_lit;
        return Ok(true);
    }
    // At this point we know that none of the watched literals are sat
    let mut k: usize = 2;
    let clause_len: usize = clause.len();
    let mut search = clause.search as usize;
    while k < clause_len {
        search += 1;
        if search == clause_len {
            search = 2;
        }
        match unit_prop_check_rest(formula, trail, watches, cref, j, search, lit) {
            Err(_) => {}
            Ok(_) => {
                formula[cref].search = search as u32;
                return Ok(false);
            }
        }
        k += 1;
    }
    *ticks += 1;
    if other_lit.lit_unsat(&trail.assignments) {
        return Err(cref);
    }
    if formula[cref][0].lit_unset(&trail.assignments) {
        trail.enq_assignment(formula[cref][0], formula, cref);
        Ok(true)
    } else {
        trail.enq_assignment(formula[cref][1], formula, cref);
        formula[cref].swap(0, 1);
        Ok(true)
    }
}

#[inline]
fn unit_prop_current_level(
    formula: &mut Formula, trail: &mut Trail, watches: &mut Watches, lit: Lit, ticks: &mut usize,
) -> Result<(), usize> {
    let mut j = 0;
    let watchidx = lit.to_watchidx();
    while j < watches[watchidx].len() {
        let curr_watch = &watches[watchidx][j];
        if curr_watch.blocker.lit_sat(&trail.assignments) {
            j += 1;
        } else {
            let cref = curr_watch.cref;
            match unit_prop_do_outer(formula, trail, watches, cref, lit, j, ticks) {
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
    formula: &mut Formula, trail: &mut Trail, watches: &mut Watches, ticks: &mut usize,
) -> Result<(), usize> {
    let mut i = trail.curr_i;
    while i < trail.trail.len() {
        let lit = trail.trail[i];
        match unit_prop_current_level(formula, trail, watches, lit, ticks) {
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
