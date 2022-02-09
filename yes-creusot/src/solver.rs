extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::assignments::*;
use crate::clause::*;
use crate::formula::*;
use crate::lit::*;
use crate::trail::*;
use crate::watches::*;
use crate::conflict_analysis::*;

// Move unit prop? Dunno where. Is it propagating over the assignments, the formula, or is it its own thing.
// Currently leaning towards assignments, but it might also be its own thing. Ill have to think some more about it.

// Requires all clauses to be at least binary.
// Returns either () if the unit propagation went fine, or a cref if a conflict was found.
#[trusted] // Ill come back to swap and enq_assignment later
#[requires(f.invariant())]
#[requires(a.invariant(@f.num_vars))]
#[requires(trail.invariant(@f.num_vars))]
#[requires(watches.invariant(*f))]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires((@trail.trail).len() > 0)]
#[ensures(@(^f).num_vars === @f.num_vars)]
#[ensures((^f).invariant())]
#[ensures((^a).invariant(@f.num_vars))]
#[ensures((^trail).invariant(@f.num_vars))]
#[ensures((^watches).invariant(*f))]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures((@(^trail).trail).len() === (@trail.trail).len())]
fn unit_propagate(f: &mut Formula, a: &mut Assignments, trail: &mut Trail, watches: &mut Watches) -> Result<(), usize> {
    let mut i = 0;
    let d = trail.trail.len() - 1;
    let none: Option<bool> = None; // Due to issue #163
    let old_f = Ghost::record(&f);
    let old_a = Ghost::record(&a);
    let old_w = Ghost::record(&watches);
    #[invariant(maintains_f, f.invariant())]
    #[invariant(maintains_a, a.invariant(@f.num_vars))]
    #[invariant(maintains_t, trail.invariant(@f.num_vars))]
    #[invariant(maintains_w, watches.invariant(*f))]
    #[invariant(num_vars, @f.num_vars === @(@old_f).num_vars)]
    #[invariant(trail_len, (@trail.trail).len() > 0)]
    #[invariant(propha, ^a === ^@old_a)]
    #[invariant(prophw, ^watches === ^@old_w)]
    #[invariant(prophf, ^f === ^@old_f)]
    while i < trail.trail[d].len() {
        let mut j = 0;
        let lit = trail.trail[d][i];
        #[invariant(maintains_f2, f.invariant())]
        #[invariant(maintains_a2, a.invariant(@f.num_vars))]
        #[invariant(maintains_t2, trail.invariant(@f.num_vars))]
        #[invariant(maintains_w2, watches.invariant(*f))]
        #[invariant(num_vars2, @f.num_vars === @(@old_f).num_vars)]
        #[invariant(trail_len2, (@trail.trail).len() > 0)]
        #[invariant(jpropha, ^a === ^@old_a)]
        #[invariant(jprophw, ^watches === ^@old_w)]
        #[invariant(jprophf, ^f === ^@old_f)]
        'outer: while j <  watches.watches[lit.to_watchidx()].len() {
            let cref = watches.watches[lit.to_watchidx()][j].cref;
            let first_lit = f.clauses[cref].0[0];
            if first_lit.is_sat(&a) {
                j += 1;
                continue;
            }
            let second_lit = f.clauses[cref].0[1];
            if second_lit.is_sat(&a) {
                // We swap to make it faster the next time
                // TODO: Swapping messes up the postconds
                //f.clauses[cref].0.swap(0, 1);
                j += 1;
                continue;
            }
            // At this point we know that none of the watched literals are sat
            let mut k = 2;
            #[invariant(maintains_f3, f.invariant())]
            #[invariant(maintains_a3, a.invariant(@f.num_vars))]
            #[invariant(maintains_t3, trail.invariant(@f.num_vars))]
            #[invariant(maintains_w3, watches.invariant(*f))]
            #[invariant(num_vars3, @f.num_vars === @(@old_f).num_vars)]
            #[invariant(trail_len3, (@trail.trail).len() > 0)]
            #[invariant(kpropha, ^a === ^@old_a)]
            #[invariant(kprophw, ^watches === ^@old_w)]
            #[invariant(kprophf, ^f === ^@old_f)]
            while k < f.clauses[cref].0.len() {
                let curr_lit = f.clauses[cref].0[k];
                // WARNING !!! DUPLICATED CODE !!! CREUSOT QUIRK
                match a.0[curr_lit.idx] {
                    Some(polarity) => {
                        if polarity == curr_lit.polarity {
                            if first_lit.idx == lit.idx {
                                //f.clauses[cref].0.swap(0, k);
                            } else {
                                //f.clauses[cref].0.swap(1, k);
                                //f.clauses[cref].0.swap(1, 0);
                            }
                            watches.update_watch(lit, curr_lit, cref, f);
                            continue 'outer;
                        }
                    },
                    None => {
                        if first_lit.idx == lit.idx {
                            //f.clauses[cref].0.swap(0, k);
                        } else {
                            //f.clauses[cref].0.swap(1, k);
                            //f.clauses[cref].0.swap(1, 0);
                        }
                        watches.update_watch(lit, curr_lit, cref, f);
                        continue 'outer;
                    }
                }
                k += 1;
            }
            // If we have gotten here, the clause is either all false or unit
            let first_res = a.0[first_lit.idx];
            match first_res {
                None => {
                    a.set_assignment(first_lit, f);
                    //trail.enq_assignment(first_lit, Reason::Long(cref));
                },
                _ => {
                    match a.0[second_lit.idx] {
                        None => {
                            //f.clauses[cref].0.swap(1, 0);
                            a.set_assignment(second_lit, f);
                            //trail.enq_assignment(second_lit, Reason::Long(cref));
                        },
                        _ => {
                            return Err(cref);
                        }
                    }

                },
            }
            j += 1;
        }
        i += 1;
    }
    Ok(())
}

#[trusted]// TMP(should check out)
#[requires((@trail.trail).len() > 0)]
#[requires(0 <= @lit.idx && @lit.idx < (@trail.vardata).len())]
#[requires(0 <= @lit.idx && @lit.idx < (@a).len())]
#[requires(trail.invariant((@trail.vardata).len()))]
#[requires(a.invariant((@trail.vardata).len()))]
#[ensures((^a).invariant((@trail.vardata).len()))]
#[ensures((^trail).invariant((@trail.vardata).len()))]
#[ensures((@(^trail).trail).len() === 1)]
pub fn learn_unit(a: &mut Assignments, trail: &mut Trail, lit: Lit, _f: &mut Formula) {
    a.cancel_until(trail, 1);
    // Postcond for cancel_until has to be updated so that the entry is guaranteed to be none.
    //proof_assert! {(@a)[@lit.idx] === None }
    a.set_assignment(lit, _f);
    trail.enq_assignment(lit, Reason::Unit);
}

#[trusted] // TMP(used to check out)
#[requires(f.invariant())]
#[requires(a.invariant(@f.num_vars))]
#[requires(trail.invariant(@f.num_vars))]
#[requires(watches.invariant(*f))]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires((@trail.trail).len() === 1)]
//#[ensures(result ==> f.eventually_sat(*a))]
//#[ensures(result === false ==> !f.eventually_sat_complete(*a))]
fn solve(f: &mut Formula, a: &mut Assignments, trail: &mut Trail, watches: &mut Watches) -> bool {
    #[invariant(maintains_f, f.invariant())]
    #[invariant(maintains_a, a.invariant(@f.num_vars))]
    #[invariant(maintains_t, trail.invariant(@f.num_vars))]
    #[invariant(maintains_w, watches.invariant(*f))]
    #[invariant(num_vars, @f.num_vars < @usize::MAX/2)]
    #[invariant(trail_len, (@trail.trail).len() > 0)]
    loop {
        #[invariant(maintains_f2, f.invariant())]
        #[invariant(maintains_a2, a.invariant(@f.num_vars))]
        #[invariant(maintains_t2, trail.invariant(@f.num_vars))]
        #[invariant(maintains_w2, watches.invariant(*f))]
        #[invariant(num_vars2, @f.num_vars < @usize::MAX/2)]
        #[invariant(trail_len2, (@trail.trail).len() > 0)]
        loop {
            match unit_propagate(f, a, trail, watches) {
                Ok(_) => { break; },
                Err(cref) => {
                    match analyze_conflict(f, a, trail, cref) {
                        Conflict::Ground => { return false; },
                        Conflict::Unit(lit) => {
                            learn_unit(a, trail, lit, f);
                        }
                        Conflict::Learned(level, lit, clause) => {
                            a.cancel_until(trail, level);
                            trail.trail.push(Vec::new());
                            //proof_assert! {(@a)[@lit.idx] === None } // Only thing missing. Needs to be ensured by cancel_until
                            a.set_assignment(lit, f);
                            let cref = f.add_clause(&Clause(clause), watches);
                            trail.enq_assignment(lit, Reason::Long(cref));
                        }
                    }
                },
            }
        }
        if let Some(lit) = a.find_unassigned_lit() {
            let lit = lit; // Due to issue #273
            trail.trail.push(Vec::new());
            a.set_assignment(lit, f);
            trail.enq_assignment(lit, Reason::Decision);
        } else {
            return true;
        } 
    }
}

#[requires(f.invariant())]
#[requires(@f.num_vars < @usize::MAX/2)]
pub fn solver(f: &mut Formula) -> bool {
    f.remove_duplicates();
    if f.num_vars == 0 {
        return true;
    }
    let mut assignments = Assignments::init_assignments(f);
    let mut trail = Trail::new(f.num_vars);
    let mut watches = Watches::new(f);
    if !watches.init_watches(f, &mut trail, &mut assignments) {
        return false; 
    }
    solve(f, &mut assignments, &mut trail, &mut watches)
}
