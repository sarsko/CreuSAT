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
fn unit_propagate(f: &mut Formula, a: &mut Assignments, d: usize, trail: &mut Trail, watches: &mut Watches) -> Result<(), usize> {
    let mut i = 0;
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
                trail.enq_assignment(first_lit, d, Reason::Long(cref));
            }
            else if a.0[second_lit.idx] == None {
                f.clauses[cref].0.swap(1, 0);
                a.set_assignment(second_lit);
                trail.enq_assignment(second_lit, d, Reason::Long(cref));
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

fn solve(f: &mut Formula, a: &mut Assignments, trail: &mut Trail, watches: &mut Watches) -> bool {
    let mut decisionlevel = 0;
    loop {
        loop {
            match unit_propagate(f, a, decisionlevel, trail, watches) {
                Ok(_) => { break; },
                Err(cref) => {
                    match analyze_conflict(f, a, trail, decisionlevel, cref) {
                        Conflict::Ground => { return false; },
                        Conflict::Unit(lit) => {
                            a.cancel_until(trail, trail.trail.len(), 1);
                            a.set_assignment(lit);
                            trail.enq_assignment(lit, trail.trail.len()-1, Reason::Unit);
                            decisionlevel = trail.trail.len() - 1 ;
                        }
                        Conflict::Learned(level, lit, clause) => {
                            a.cancel_until(trail, trail.trail.len(), level);
                            trail.trail.push(Vec::new());
                            a.set_assignment(lit);
                            let cref = f.add_clause(&Clause(clause), watches);
                            trail.enq_assignment(lit, trail.trail.len()-1, Reason::Long(cref));
                            decisionlevel = trail.trail.len() - 1;
                        }
                    }
                },
            }
        }
        if let Some(lit) = a.find_unassigned_lit() {
            trail.trail.push(Vec::new());
            a.set_assignment(lit);
            decisionlevel += 1;
            trail.enq_assignment(lit, decisionlevel, Reason::Decision);
        } else {
            return true;
        } 
    }
}

pub fn solver(f: &mut Formula) -> bool {
    if f.num_vars == 0 {
        return true;
    }
    let mut watches = Watches::new(f.num_vars);
    watches.init_watches(f);
    solve(f, &mut Assignments::init_assignments(f), &mut Trail::new(f.num_vars), &mut watches)
}
