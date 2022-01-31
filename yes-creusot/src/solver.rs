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
#[trusted]
fn unit_propagate(f: &mut Formula, a: &mut Assignments, trail: &mut Trail, watches: &mut Watches) -> Result<(), usize> {
    let mut i = 0;
    let d = trail.trail.len() - 1;
    while i < trail.trail[d].len() {
        let mut j = 0;
        let lit = trail.trail[d][i];
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
                f.clauses[cref].0.swap(0, 1);
                j += 1;
                continue;
            }
            // At this point we know that none of the watched literals are sat
            let mut k = 2;
            while k < f.clauses[cref].0.len() {
                let curr_lit = f.clauses[cref].0[k];
                if a.0[curr_lit.idx] == None || a.0[curr_lit.idx] == Some(curr_lit.polarity) {
                    if first_lit.idx == lit.idx {
                        f.clauses[cref].0.swap(0, k);
                    } else {
                        f.clauses[cref].0.swap(1, k);
                        f.clauses[cref].0.swap(1, 0);
                    }
                    watches.update_watch(lit, curr_lit, cref);
                    continue 'outer;
                }
                k += 1;
            }
            // If we have gotten here, the clause is either all false or unit
            if a.0[first_lit.idx] == None {
                a.set_assignment(first_lit);
                trail.enq_assignment(first_lit, Reason::Long(cref));
            }
            else if a.0[second_lit.idx] == None {
                f.clauses[cref].0.swap(1, 0);
                a.set_assignment(second_lit);
                trail.enq_assignment(second_lit, Reason::Long(cref));
            }
            else {
                return Err(cref);
            }
            j += 1;
        }
        i += 1;
    }
    Ok(())
}

#[trusted]
#[requires((@trail.trail).len() > 0)] // This is partially wrong
#[requires(0 <= @lit.idx && @lit.idx < (@trail.vardata).len())]
#[requires(0 <= @lit.idx && @lit.idx < (@a).len())]
#[requires(trail.invariant((@trail.vardata).len()))]
#[requires(a.invariant((@trail.vardata).len()))]
pub fn learn_unit(a: &mut Assignments, trail: &mut Trail, lit: Lit) {
    a.cancel_until(trail, 1);
    // Postcond for cancel_until has to be updated so that the entry is guaranteed to be none.
    proof_assert! {(@a)[@lit.idx] === None }
    a.set_assignment(lit);
    trail.enq_assignment(lit, Reason::Unit);
}

#[trusted]
fn solve(f: &mut Formula, a: &mut Assignments, trail: &mut Trail, watches: &mut Watches) -> bool {
    loop {
        loop {
            let dlevel = trail.trail.len() - 1;
            match unit_propagate(f, a, trail, watches) {
                Ok(_) => { break; },
                Err(cref) => {
                    match analyze_conflict(f, a, trail, cref) {
                        Conflict::Ground => { return false; },
                        Conflict::Unit(lit) => {
                            learn_unit(a, trail, lit);
                        }
                        Conflict::Learned(level, lit, clause) => {
                            a.cancel_until(trail, level);
                            trail.trail.push(Vec::new());
                            a.set_assignment(lit);
                            let cref = f.add_clause(&Clause(clause), watches);
                            trail.enq_assignment(lit, Reason::Long(cref));
                        }
                    }
                },
            }
        }
        if let Some(lit) = a.find_unassigned_lit() {
            trail.trail.push(Vec::new());
            a.set_assignment(lit);
            trail.enq_assignment(lit, Reason::Decision);
        } else {
            return true;
        } 
    }
}

pub fn solver(f: &mut Formula) -> bool {
    f.remove_duplicates();
    if f.num_vars == 0 {
        return true;
    }
    let mut assignments = Assignments::init_assignments(f);
    let mut trail = Trail::new(f.num_vars);
    let mut watches = Watches::new(f.num_vars);
    if !watches.init_watches(f, &mut trail, &mut assignments) {
        return false; 
    }
    solve(f, &mut assignments, &mut trail, &mut watches)
}
