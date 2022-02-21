use crate::assignments::*;
use crate::clause::*;
use crate::formula::*;
use crate::lit::*;
use crate::trail::*;
use crate::watches::*;
use crate::conflict_analysis::*;

use std::time::Instant;

// Move unit prop? Dunno where. Is it propagating over the assignments, the formula, or is it its own thing.
// Currently leaning towards assignments, but it might also be its own thing. Ill have to think some more about it.

// Requires all clauses to be at least binary.
// Returns either () if the unit propagation went fine, or a cref if a conflict was found.
fn unit_propagate(f: &mut Formula, a: &mut Assignments, trail: &mut Trail, watches: &mut Watches) -> Result<(), usize> {
    let mut i = 0;
    let d = trail.trail.len() - 1;
    while i < trail.trail[d].len() {
        let mut j = 0;
        let lit = trail.trail[d][i];
        let watchidx = lit.to_watchidx();
        'outer: while j < watches.watches[watchidx].len() {
            let cref = watches.watches[watchidx][j].cref;
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
            let clause_len = f.clauses[cref].0.len();
            while k < clause_len {
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
            } else if a.0[second_lit.idx] == None {
                f.clauses[cref].0.swap(1, 0);
                a.set_assignment(second_lit);
                trail.enq_assignment(second_lit, Reason::Long(cref));
            } else {
                return Err(cref);
            }
            j += 1;
        }
        i += 1;
    }
    Ok(())
}

pub fn learn_unit(a: &mut Assignments, trail: &mut Trail, lit: Lit) {
    a.cancel_until(trail, trail.trail.len(), 1);
    a.set_assignment(lit);
    trail.enq_assignment(lit, Reason::Unit);
}

fn solve(f: &mut Formula, a: &mut Assignments, trail: &mut Trail, watches: &mut Watches) -> bool {
    let mut cntr = 0;
    loop {
        loop {
        let start = Instant::now();
            match unit_propagate(f, a, trail, watches) {
                Ok(_) => { 
        cntr += start.elapsed().as_nanos();
                    break; },
                Err(cref) => {
        cntr += start.elapsed().as_nanos();
                    match analyze_conflict(f, a, trail, cref) {
                        Conflict::Ground => { 
                            println!("{}", cntr as f64 /1000000000.0);
                            return false; },
                        Conflict::Unit(lit) => {
                            learn_unit(a, trail, lit);
                        }
                        Conflict::Learned(level, lit, clause) => {
                            a.cancel_until(trail, trail.trail.len(), level);
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
            println!("{}", cntr as f64 /1000000000.0);
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
