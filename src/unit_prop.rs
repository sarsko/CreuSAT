extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::lit::*;
use crate::clause::*;
use crate::assignments::*;
use crate::formula::*;
use crate::trail::*;
use crate::watches::*;

#[trusted]
fn unit_prop_check_rest(f: &mut Formula, a: &mut Assignments, trail: &mut Trail, watches: &mut Watches, cref: usize, j: usize, k: usize, watchidx: usize,
first_lit: Lit, second_lit: Lit, lit: Lit) -> Result<(), ()> {
    let curr_lit = f.clauses[cref].rest[k];
    if curr_lit.lit_unset(a) || curr_lit.lit_sat(a) { // Can swap to !unsat
        if first_lit.idx == lit.idx {
            f.clauses[cref].rest[0] = curr_lit;
            f.clauses[cref].rest[k] = first_lit;
        } else {
            f.clauses[cref].rest[0] = curr_lit;
            f.clauses[cref].rest[k] = second_lit;
            f.clauses[cref].rest[1] = first_lit;
        }
        // Update watch inlined
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
        return Err(()); // dont increase j
    }
    return Ok(());
}

#[trusted]
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
    Ok(true) => !(^f).unsat(^a),
    Ok(false) => !(^f).unsat(^a),
    Err(n) => @n < (@(^f).clauses).len() && (^f).unsat(^a) && (@(^f).clauses)[@n].unsat(^a),
})]
#[ensures((*a).compatible(^a))]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures((^f).invariant())]
#[ensures((^trail).invariant(^f))]
#[ensures((^a).invariant(^f))]
#[ensures(f.equisat_compatible(^f))]
fn unit_prop_do_outer(f: &mut Formula, a: &mut Assignments, trail: &mut Trail, watches: &mut Watches, j: usize, watchidx: usize, lit: Lit) -> Result<bool, usize> {
    let cref = watches.watches[watchidx][j].cref;
    let first_lit = f.clauses[cref].rest[0];
    if first_lit.lit_sat(&a) {
        return Ok(true);
    }
    let second_lit = f.clauses[cref].rest[1];
    if second_lit.lit_sat(&a) {
        // We swap to make it faster the next time
        f.clauses[cref].rest[0] = second_lit;
        f.clauses[cref].rest[1] = first_lit;
        return Ok(true);
    }
    // At this point we know that none of the watched literals are sat
    let mut k = 2;
    let clause_len = f.clauses[cref].rest.len();
    while k < clause_len {
        match unit_prop_check_rest(f, a, trail, watches, cref, j, k, watchidx, first_lit, second_lit, lit) {
            Ok(_) => {},
            Err(_) => {
                return Ok(false);
            }
        }
        k += 1;
    }
    // If we have gotten here, the clause is either all false or unit
    if first_lit.lit_unset(a) {
        a.set_assignment(first_lit, f);
        trail.enq_assignment(first_lit, Reason::Long(cref), f, a);
    } else if second_lit.lit_unset(a) {
        f.clauses[cref].rest.swap(0,1);
        a.set_assignment(second_lit, f);
        trail.enq_assignment(second_lit, Reason::Long(cref), f, a);
    } else {
        return Err(cref);
    }
    return Ok(true);
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
    #[invariant(f_equi, (@old_f).equisat_compatible(*f))]
    #[invariant(f_inv, f.invariant())]
    #[invariant(ass_inv, a.invariant(*f))]
    #[invariant(a_compat, (@old_a).compatible(*a))]
    #[invariant(nvars_unch, @f.num_vars === @(@old_f).num_vars)]
    #[invariant(proph_t, ^trail === ^@old_trail)]
    #[invariant(proph_f, ^f === ^@old_f)]
    #[invariant(proph_a, ^a === ^@old_a)]
    #[invariant(proph_w, ^watches === ^@old_w)]
    while j < watches.watches[watchidx].len() {
        match unit_prop_do_outer(f, a, trail, watches, j, watchidx, lit) {
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