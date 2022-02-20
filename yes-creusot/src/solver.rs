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

#[logic]
#[requires(0 <= i && i < (@c).len())]
#[requires(0 <= j && j < (@c).len())]
#[requires((@c).len() === (@c2).len())]
#[requires((@c2)[i] === (@c)[j])]
#[requires((@c2)[j] === (@c)[i])]
#[requires(forall<k: Int> 0 <= k && k < (@c).len() && k != j && k != i ==>
    (@c2)[k] === (@c)[k])]
#[requires(c2.invariant(f))]
#[ensures(c.invariant(f))]
fn lemma_swap_ok(c: Clause, c2: Clause, i: Int, j: Int, f: Formula) {}

#[trusted] // Checks out(but the trail invariant takes some time)
#[requires(@cref < (@f.clauses).len())]
//#[requires(@i < @j)]
#[requires(@j < (@(@f.clauses)[@cref]).len() && @i < (@(@f.clauses)[@cref]).len())]
#[requires(f.invariant())]
#[requires(_t.invariant(*f))]
#[ensures((^f).invariant())]
#[ensures(_t.invariant(^f))]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures((@(^f).clauses).len() === (@f.clauses).len())]
#[ensures(forall<i: Int> 0 <= i && i < (@(^f).clauses).len() ==>
    (@(@(^f).clauses)[i]).len() === (@(@f.clauses)[i]).len())] // Needed for watches, can be rewritten
#[ensures((@(@(^f).clauses)[@cref]).exchange(@(@f.clauses)[@cref], @i, @j))]
fn swap_lits(f: &mut Formula, cref: usize, i: usize, j: usize, _t: &Trail) {
    let old_c = Ghost::record(&f.clauses[cref]);
    f.clauses[cref].0.swap(i, j);
    proof_assert!(lemma_swap_ok(((@f.clauses)[@cref]), @old_c, @i, @j, *f);true);
}

// Move unit prop? Dunno where. Is it propagating over the assignments, the formula, or is it its own thing.
// Currently leaning towards assignments, but it might also be its own thing. Ill have to think some more about it.

// Requires all clauses to be at least binary.
// Returns either () if the unit propagation went fine, or a cref if a conflict was found.
//#[trusted] // Checks out
#[requires(f.invariant())]
#[requires(a.invariant(@f.num_vars))]
#[requires(trail.invariant(*f))]
#[requires(watches.invariant(*f))]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires((@trail.trail).len() > 0)]
#[ensures((^f).invariant())]
#[ensures((^a).invariant(@f.num_vars))]
#[ensures((^trail).invariant(^f))]
#[ensures((^watches).invariant(^f))]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures((@(^f).clauses).len() === (@f.clauses).len())]
#[ensures((@(^trail).trail).len() === (@trail.trail).len())]
fn unit_propagate(f: &mut Formula, a: &mut Assignments, trail: &mut Trail, watches: &mut Watches) -> Result<(), usize> {
    let mut i: usize = 0;
    let d: usize = trail.trail.len() - 1;
    let old_f = Ghost::record(&f);
    let old_a = Ghost::record(&a);
    let old_w = Ghost::record(&watches);
    let old_t = Ghost::record(&trail);
    #[invariant(maintains_f, f.invariant())]
    #[invariant(f_len, (@f.clauses).len() === (@(@old_f).clauses).len())]
    #[invariant(maintains_a, a.invariant(@f.num_vars))]
    #[invariant(maintains_t, trail.invariant(*f))]
    #[invariant(maintains_w, watches.invariant(*f))]
    #[invariant(num_vars, @f.num_vars === @(@old_f).num_vars)]
    #[invariant(trail_len, (@trail.trail).len() === (@(@old_t).trail).len())]
    #[invariant(propha, ^a === ^@old_a)]
    #[invariant(prophw, ^watches === ^@old_w)]
    #[invariant(prophf, ^f === ^@old_f)]
    #[invariant(propht, ^trail === ^@old_t)]
    #[invariant(dless, 0<= @d && @d < (@trail.trail).len())]
    #[invariant(iless, 0 <= @i && @i <= (@(@trail.trail)[@d]).len())]
    while i < trail.trail[d].len() {
        let mut j = 0;
        let lit: Lit = trail.trail[d][i];
        let old_trail_end = Ghost::record(&(trail.trail[d]));
        proof_assert!((@watches.watches).len() === 2 * @f.num_vars);
        proof_assert!(@f.num_vars > @lit.idx);
        proof_assert!(lemma_watchidx_less(lit, @f.num_vars);(@watches.watches).len() > lit.to_watchidx_logic());

        #[invariant(maintains_f2, f.invariant())]
        #[invariant(f_len2, (@f.clauses).len() === (@(@old_f).clauses).len())]
        #[invariant(maintains_a2, a.invariant(@f.num_vars))]
        #[invariant(maintains_t2, trail.invariant(*f))]
        #[invariant(maintains_w2, watches.invariant(*f))]
        #[invariant(num_vars2, @f.num_vars === @(@old_f).num_vars)]
        #[invariant(trail_len2, (@trail.trail).len() === (@(@old_t).trail).len())]
        #[invariant(jpropha, ^a === ^@old_a)]
        #[invariant(jprophw, ^watches === ^@old_w)]
        #[invariant(jprophf, ^f === ^@old_f)]
        #[invariant(jpropht, ^trail === ^@old_t)]
        #[invariant(dless2, @d < (@trail.trail).len())]
        #[invariant(iless2, 0 <= @i && @i <= (@(@trail.trail)[@d]).len())]
        #[invariant(trail_end_same, (@(@trail.trail)[@d]).len() >= (@@old_trail_end).len())]
        'outer: while j < watches.watches[lit.to_watchidx()].len() {
            proof_assert!((@watches.watches).len() === 2 * @f.num_vars);
            proof_assert!(@f.num_vars > @lit.idx);
            proof_assert!(lemma_watchidx_less(lit, @f.num_vars);(@watches.watches).len() > lit.to_watchidx_logic());
            let cref = watches.watches[lit.to_watchidx()][j].cref;
            let first_lit = f.clauses[cref].0[0];
            proof_assert!(@first_lit.idx < (@a).len());
            if first_lit.is_sat(&a) {
                j += 1;
                continue;
            }
            let second_lit = f.clauses[cref].0[1];
            proof_assert!(@second_lit.idx < (@a).len());
            if second_lit.is_sat(&a) {
                // We swap to make it faster the next time
                swap_lits(f, cref, 0, 1, trail);
                j += 1;
                continue;
            }
            // At this point we know that none of the watched literals are sat
            let mut k: usize = 2;
            #[invariant(maintains_f3, f.invariant())]
            #[invariant(f_len2, (@f.clauses).len() === (@(@old_f).clauses).len())]
            #[invariant(maintains_a3, a.invariant(@f.num_vars))]
            #[invariant(maintains_t3, trail.invariant(*f))]
            #[invariant(maintains_w3, watches.invariant(*f))]
            #[invariant(num_vars3, @f.num_vars === @(@old_f).num_vars)]
            #[invariant(trail_len3, (@trail.trail).len() === (@(@old_t).trail).len())]
            #[invariant(kpropha, ^a === ^@old_a)]
            #[invariant(kprophw, ^watches === ^@old_w)]
            #[invariant(kprophf, ^f === ^@old_f)]
            #[invariant(jpropht, ^trail === ^@old_t)]
            #[invariant(kbound, @k <= (@(@f.clauses)[@cref]).len())]
            #[invariant(dless3, @d < (@trail.trail).len())]
            #[invariant(iless3, 0 <= @i && @i <= (@(@trail.trail)[@d]).len())]
            #[invariant(trail_end_same2, (@(@trail.trail)[@d]).len() >= (@@old_trail_end).len())]
            while k < f.clauses[cref].0.len() {
                let curr_lit = f.clauses[cref].0[k];
                // WARNING !!! DUPLICATED CODE !!! CREUSOT QUIRK
                match a.0[curr_lit.idx] {
                    Some(polarity) => {
                        if polarity == curr_lit.polarity {
                            if first_lit.idx == lit.idx {
                                swap_lits(f, cref, 0, k, trail);
                            } else {
                                swap_lits(f, cref, 1, k, trail);
                                swap_lits(f, cref, 1, 0, trail);
                            }
                            proof_assert!(@cref === @(@(@watches.watches)[lit.to_watchidx_logic()])[@j].cref);

                            proof_assert!(exists<j: Int> 0 <= j && j < (@(@watches.watches)[lit.to_watchidx_logic()]).len() && (@(@(@watches.watches)[lit.to_watchidx_logic()])[j].cref) === @cref);
                            proof_assert!(watches.invariant(*f));
                            proof_assert!(@lit.idx < @usize::MAX/2);
                            proof_assert!(@curr_lit.idx < @usize::MAX/2);
                            proof_assert!(lit.to_watchidx_logic() < (@watches.watches).len());
                            proof_assert!(curr_lit.to_neg_watchidx_logic() < (@watches.watches).len());
                            watches.update_watch(lit, curr_lit, cref, f);
                            continue 'outer;
                        }
                    },
                    None => {
                        if first_lit.idx == lit.idx {
                            swap_lits(f, cref, 0, k, trail);
                        } else {
                            swap_lits(f, cref, 1, k, trail);
                            swap_lits(f, cref, 1, 0, trail);
                        }
                        proof_assert!(@cref === @(@(@watches.watches)[lit.to_watchidx_logic()])[@j].cref);

                        proof_assert!(exists<j: Int> 0 <= j && j < (@(@watches.watches)[lit.to_watchidx_logic()]).len() && (@(@(@watches.watches)[lit.to_watchidx_logic()])[j].cref) === @cref);
                        proof_assert!(watches.invariant(*f));
                        proof_assert!(@lit.idx < @usize::MAX/2);
                        proof_assert!(@curr_lit.idx < @usize::MAX/2);
                        proof_assert!(lit.to_watchidx_logic() < (@watches.watches).len());
                        proof_assert!(curr_lit.to_neg_watchidx_logic() < (@watches.watches).len());
                        watches.update_watch(lit, curr_lit, cref, f);
                        continue 'outer;
                    }
                }
                k += 1;
            }
            // If we have gotten here, the clause is either all false or unit
            match a.0[first_lit.idx]{
                None => {
                    a.set_assignment(first_lit, f);
                    trail.enq_assignment(first_lit, Reason::Long(cref), f);
                },
                _ => {
                    match a.0[second_lit.idx] {
                        None => {
                            swap_lits(f, cref, 1, 0, trail);
                            a.set_assignment(second_lit, f);
                            trail.enq_assignment(second_lit, Reason::Long(cref), f);
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

#[trusted]// Checks out
#[requires((@trail.trail).len() > 0)]
#[requires(0 <= @lit.idx && @lit.idx < (@trail.vardata).len())]
#[requires(0 <= @lit.idx && @lit.idx < (@a).len())]
#[requires(trail.invariant(*_f))]
#[requires(a.invariant(@_f.num_vars))]
#[ensures((^a).invariant(@_f.num_vars))]
#[ensures((^trail).invariant(*_f))]
#[ensures((@(^trail).trail).len() === 1)]
pub fn learn_unit(a: &mut Assignments, trail: &mut Trail, lit: Lit, _f: &Formula) {
    a.cancel_until(trail, 1, _f);
    // Postcond for cancel_until has to be updated so that the entry is guaranteed to be none.
    //proof_assert! {(@a)[@lit.idx] === None }
    a.set_assignment(lit, _f);
    trail.enq_assignment(lit, Reason::Unit, _f);
}

#[trusted] // Used to check out(doesnt anymore)
//#[requires(@f.num_vars < @usize::MAX/2)]
#[requires((@f.clauses).len() > 0)]
#[requires(f.invariant())]
#[requires(a.invariant(@f.num_vars))]
#[requires(trail.invariant(*f))]
#[requires(watches.invariant(*f))]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires((@trail.trail).len() === 1)]
//#[ensures(result ==> f.eventually_sat(*a))]
//#[ensures(result === false ==> !f.eventually_sat_complete(*a))]
fn solve(f: &mut Formula, a: &mut Assignments, trail: &mut Trail, watches: &mut Watches) -> bool {
    let old_f = Ghost::record(&f);
    let old_a = Ghost::record(&a);
    let old_w = Ghost::record(&watches);
    #[invariant(maintains_f, f.invariant())]
    #[invariant(maintains_a, a.invariant(@f.num_vars))]
    #[invariant(maintains_t, trail.invariant(*f))]
    #[invariant(maintains_w, watches.invariant(*f))]
    #[invariant(num_vars, @f.num_vars < @usize::MAX/2)]
    #[invariant(clauses, (@f.clauses).len() > 0)]
    #[invariant(trail_len, (@trail.trail).len() > 0)]
    #[invariant(propha, ^a === ^@old_a)]
    #[invariant(prophw, ^watches === ^@old_w)]
    #[invariant(prophf, ^f === ^@old_f)]
    loop {
        #[invariant(maintains_f2, f.invariant())]
        #[invariant(maintains_a2, a.invariant(@f.num_vars))]
        #[invariant(maintains_t2, trail.invariant(*f))]
        #[invariant(maintains_w2, watches.invariant(*f))]
        #[invariant(num_vars2, @f.num_vars < @usize::MAX/2)]
        #[invariant(clauses2, (@f.clauses).len() > 0)]
        #[invariant(trail_len2, (@trail.trail).len() > 0)]
        #[invariant(propha2, ^a === ^@old_a)]
        #[invariant(prophw2, ^watches === ^@old_w)]
        #[invariant(prophf2, ^f === ^@old_f)]
        loop {
            match unit_propagate(f, a, trail, watches) {
                Ok(_) => { break; },
                Err(cref) => {
                    match analyze_conflict(f, a, trail, cref, watches) {
                        Conflict::Ground => { return false; },
                        Conflict::Unit(lit) => {
                            learn_unit(a, trail, lit, f);
                        }
                        Conflict::Learned(level, lit, clause) => {
                            a.cancel_until(trail, level, f);
                            trail.trail.push(Vec::new());
                            //proof_assert! {(@a)[@lit.idx] === None } // Only thing missing. Needs to be ensured by cancel_until
                            a.set_assignment(lit, f);
                            let cref = f.add_clause(&Clause(clause), watches);
                            trail.enq_assignment(lit, Reason::Long(cref), f);
                        }
                    }
                },
            }
        }
        if let Some(lit) = a.find_unassigned_lit() {
            let lit = lit; // Due to issue #273
            trail.trail.push(Vec::new());
            a.set_assignment(lit, f);
            trail.enq_assignment(lit, Reason::Decision, f);
        } else {
            return true;
        } 
    }
}

#[requires(f.invariant())]
#[requires(@f.num_vars < @usize::MAX/2)]
pub fn solver(f: &mut Formula) -> bool {
    f.remove_duplicates();
    if f.num_vars == 0 || f.clauses.len() == 0 {
        return true;
    }
    let mut assignments = Assignments::init_assignments(f);
    let mut trail = Trail::new(f);
    let mut watches = Watches::new(f);
    if !watches.init_watches(f, &mut trail, &mut assignments) {
        return false; 
    }
    solve(f, &mut assignments, &mut trail, &mut watches)
}
