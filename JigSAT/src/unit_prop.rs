use crate::{formula::*, lit::*, trail::*, watches::*};


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

fn swap(f: &mut Formula, trail: &Trail, watches: &Watches, cref: usize, j: usize, k: usize) {
    f.clauses[cref].rest.swap(j, k);
}


fn unit_prop_do_outer(
    f: &mut Formula, trail: &mut Trail, watches: &mut Watches, cref: usize, lit: Lit, j: usize,
) -> Result<bool, usize> {
    let first_lit = f.clauses[cref].rest[0];
    if first_lit.lit_sat(&trail.assignments) {
        return Ok(true);
    }
    let second_lit = f.clauses[cref].rest[1];
    if second_lit.lit_sat(&trail.assignments) {
        // We swap to make it faster the next time
        //swap_zero_one(f, trail, watches, cref, lit, j);
        swap(f, trail, watches, cref, 0, 1);
        return Ok(true);
    }
    // At this point we know that none of the watched literals are sat
    let mut k: usize = 2;
    let clause_len: usize = f.clauses[cref].rest.len();
    while k < clause_len {
        match unit_prop_check_rest(f, trail, watches, cref, j, k, lit) {
            Err(_) => {
            }
            Ok(_) => {
                return Ok(false);
            }
        }
        k += 1;
    }
    if first_lit.lit_unset(&trail.assignments) {
        let step = Step {
            lit: first_lit,
            //lit: f.clauses[cref].rest[0],
            decision_level: trail.decision_level(),
            reason: Reason::Long(cref),
        };

        trail.enq_assignment(step, f);
        return Ok(true);
    } else if second_lit.lit_unset(&trail.assignments) {
        let step = Step { lit: second_lit, decision_level: trail.decision_level(), reason: Reason::Long(cref) };

        trail.enq_assignment(step, f);
        // slowdown in swapping
        //f.clauses[cref].rest.swap(0,1);
        return Ok(true);
    } else {
        return Err(cref);
    }
}

fn unit_prop_current_level(f: &mut Formula, trail: &mut Trail, watches: &mut Watches, lit: Lit) -> Result<(), usize> {
    let mut j = 0;
    let watchidx = lit.to_watchidx();
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

pub fn unit_propagate(f: &mut Formula, trail: &mut Trail, watches: &mut Watches) -> Result<(), usize> {
    let mut i = trail.curr_i;
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
