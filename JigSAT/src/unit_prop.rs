use crate::{formula::*, lit::*, trail::*, watches::*};


fn unit_prop_check_rest(
    f: &mut Formula, trail: &Trail, watches: &mut Watches, cref: usize, j: usize, k: usize, lit: Lit, other_lit: Lit,
) -> Result<bool, ()> {
    return Err(());
}

#[inline(always)]
fn swap(f: &mut Formula, _trail: &Trail, _watches: &Watches, cref: usize, j: usize, k: usize) {
    f[cref].rest.swap(j, k);
}


fn unit_prop_do_outer(
    f: &mut Formula, trail: &mut Trail, watches: &mut Watches, cref: usize, lit: Lit, j: usize,
) -> Result<bool, usize> {
    let clause = &mut f[cref];
    let neg_lit = !lit;
    let other_lit = neg_lit.select_other(clause[0], clause[1]);
    if other_lit.lit_sat(&trail.assignments) {
        watches[lit.to_watchidx()][j].blocker = other_lit;
        return Ok(true);
    }
    // At this point we know that none of the watched literals are sat
    let mut k: usize = 2;
    let clause_len: usize = clause.len();
    let mut search = clause.search;
    while k < clause_len {
        let curr_lit = clause[search];
        if !(curr_lit.lit_unsat(&trail.assignments)){
            if curr_lit.lit_sat(&trail.assignments) {
                watches[lit.to_watchidx()][j].blocker = curr_lit;
                //clause.search = search;
                clause.search = search;
                return Ok(true);
            }
            watches[lit.to_watchidx()][j].blocker = other_lit;
            clause[0] = curr_lit;
            clause[1] = other_lit;
            clause[search] = neg_lit;

            let end = watches.watches[lit.to_watchidx()].len() - 1;
            watches.watches[lit.to_watchidx()].swap(j, end);
            match watches.watches[lit.to_watchidx()].pop() {
                Some(w) => {
                    watches.watches[curr_lit.to_neg_watchidx()].push(w);
                }
                None => {
                    unreachable!();
                }
    }
            //update_watch(f, trail, watches, cref, j, 0, lit);

            clause.search = search;
            return Ok(false); // dont increase j
        }
        k += 1;
        search += 1;
        if search == clause_len {
            search = 2;
        }
    }
    if other_lit.lit_unsat(&trail.assignments) {
        return Err(cref);
    }
    clause[0] = other_lit;
    clause[1] = neg_lit;
    let step = Step {
        lit: other_lit,
        decision_level: trail.decision_level(),
        reason: Reason::Long(cref),
    };

    trail.enq_assignment(step, f);
    return Ok(true);
}

fn unit_prop_current_level(f: &mut Formula, trail: &mut Trail, watches: &mut Watches, lit: Lit) -> Result<(), usize> {
    let mut j = 0;
    let watchidx = lit.to_watchidx();
    while j < watches.watches[watchidx].len() {
        let curr_watch = &watches.watches[watchidx][j];
        if curr_watch.blocker.lit_sat(&trail.assignments) {
            j += 1;
        } else {
            let cref = curr_watch.cref;
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
