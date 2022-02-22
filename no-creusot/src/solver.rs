use crate::assignments::*;
use crate::clause::*;
use crate::formula::*;
use crate::lit::*;
use crate::trail::*;
use crate::watches::*;
use crate::conflict_analysis::*;
use crate::decision::*;
use crate::luby::*;

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
            let first_lit = f.clauses[cref].first;
            if first_lit.is_sat(&a) {
                j += 1;
                continue;
            }
            let second_lit = f.clauses[cref].second;
            if second_lit.is_sat(&a) {
                // We swap to make it faster the next time
                f.clauses[cref].first = second_lit;
                f.clauses[cref].second = first_lit;
                j += 1;
                continue;
            }
            // At this point we know that none of the watched literals are sat
            let mut k = 0;
            let clause_len = f.clauses[cref].rest.len();
            while k < clause_len {
                let curr_lit = f.clauses[cref].rest[k];
                if a.0[curr_lit.idx] >= 2 || a.0[curr_lit.idx] == curr_lit.polarity as u8 { // Todo change
                    if first_lit.idx == lit.idx {
                        f.clauses[cref].first = curr_lit;
                        f.clauses[cref].rest[k] = first_lit;
                    } else {
                        f.clauses[cref].first = curr_lit;
                        f.clauses[cref].rest[k] = second_lit;
                        f.clauses[cref].second = first_lit;
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
                    continue 'outer;
                }
                k += 1;
            }
            // If we have gotten here, the clause is either all false or unit
            if a.0[first_lit.idx] >= 2 {
                a.set_assignment(first_lit);
                trail.enq_assignment(first_lit, Reason::Long(cref));
            } else if a.0[second_lit.idx] >= 2 {
                f.clauses[cref].first = second_lit;
                f.clauses[cref].second = first_lit;
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

pub fn learn_unit(a: &mut Assignments, trail: &mut Trail, lit: Lit, decisions: &mut Decisions) {
    a.cancel_until(trail, trail.trail.len(), 1, decisions);
    //a.cancel_long(trail);
    a.set_assignment(lit);
    trail.enq_assignment(lit, Reason::Unit);
}

fn solve(f: &mut Formula, a: &mut Assignments, trail: &mut Trail, watches: &mut Watches, decisions: &mut Decisions) -> bool {
    let mut restart_delay = 10000;
    let mut num_conflicts = 0;
    let scale = 128;
    let mut luby = Luby::default();
    loop {
        loop {
            if num_conflicts == restart_delay {
                num_conflicts = 0;
                restart_delay += scale * luby.advance();
                a.cancel_until(trail, trail.trail.len(), 1, decisions);
            }
            match unit_propagate(f, a, trail, watches) {
                Ok(_) => { break; },
                Err(cref) => {
                    match analyze_conflict(f, a, trail, cref) {
                        Conflict::Ground => { return false; },
                        Conflict::Unit(lit) => {
                            num_conflicts += 1;
                            learn_unit(a, trail, lit, decisions);
                        }
                        Conflict::Learned(level, lit, clause) => {
                            num_conflicts += 1;
                            let cref = f.add_clause(&clause, watches);
                            decisions.increment_and_move(f, cref);
                            a.cancel_until(trail, trail.trail.len(), level, decisions);
                            trail.trail.push(Vec::new());
                            a.set_assignment(lit);
                            trail.enq_assignment(lit, Reason::Long(cref));
                        }
                    }
                },
            }
        }    
        if let Some(lit) = a.find_unassigned_lit(decisions) {
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
    let mut decisions = Decisions::new(f);
    solve(f, &mut assignments, &mut trail, &mut watches, &mut decisions)
}
