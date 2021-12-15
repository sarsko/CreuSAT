use crate::assignments::*;
use crate::clause::*;
use crate::formula::*;
use crate::lit::*;
use crate::trail::*;
use crate::watches::*;
use crate::conflict_analysis::*;

#[allow(dead_code)]
enum SatState {
    Unsat,
    Sat(Assignments),
    Unknown,
}

// Move unit prop? Dunno where. Is it propagating over the assignments, the formula, or is it its own thing.
// Currently leaning towards assignments, but it might also be its own thing. Ill have to think some more about it.

// Requires all clauses to be at least binary.
// Returns either () if the unit propagation went fine, or a cref if a conflict was found.
fn unit_propagate(f: &mut Formula, a: &mut Assignments, d: usize, trail: &mut Trail, watches: &mut Watches) -> Result<(), usize> {
    //watches.check_only_first_two_watched(f, &"TOP OF UNIT PROP");
    let mut i = 0;
    while i < trail.trail[d].len() {
        //watches.check_only_first_two_watched(f, &"START OF TRAIL LOOP");
        let mut j = 0;
        // Get the enqueued literal
        let lit = trail.trail[d][i];
        //println!("Clauses: {:?}", f.clauses);
        // Find all the clauses that could have become unit(those that watch for this assignment)
        'outer: while j <  watches.watches[lit.to_watchidx()].len() {
            //watches.check_only_first_two_watched(f, &"TOP OF OUTER");
            let cref = watches.watches[lit.to_watchidx()][j].cref;
            //println!("Propagating clause: {:?}", f.clauses[cref].0);
            let first_lit = f.clauses[cref].0[0];
            if first_lit.is_sat(&a) {
                // First watched literal is sat
                j += 1;
                continue;
            }
            let second_lit = f.clauses[cref].0[1];
            if second_lit.is_sat(&a) {
                // Second watched literal is sat
                // We swap to make it faster the next time
                f.clauses[cref].0.swap(0, 1);
                j += 1;
                continue;
            }
            //assert!(lit.idx == first_lit.idx || lit.idx == second_lit.idx);
            // At this point we know that lit is not sat, and that none of the watched literals are sat
            let mut k = 2;
            while k < f.clauses[cref].0.len() {
                let curr_lit = f.clauses[cref].0[k];
                if curr_lit.is_sat(&a) {
                    // Some other literal was true -> we swap it to the first place and watch it

                    if lit.idx == first_lit.idx {
                        f.clauses[cref].0.swap(0, k);
                    } else {
                        f.clauses[cref].0.swap(1, k);
                        f.clauses[cref].0.swap(1, 0);
                    }
                    watches.update_watch(lit, curr_lit, cref);
                    continue 'outer;
                }
                else if a.0[curr_lit.idx] == None {
                    if first_lit.idx == lit.idx {
                        f.clauses[cref].0.swap(0, k);
                    }
                    else {
                        //assert!(second_lit.idx == lit.idx);
                        f.clauses[cref].0.swap(1, k);
                    }
                    f.clauses[cref].0.swap(1, 0);
                    watches.update_watch(lit, curr_lit, cref);
                    continue 'outer;
                }
                k += 1;
            }
            // If we have gotten here, the clause is either all false or unit
            //assert!(!(a.0[first_lit.idx] == None && a.0[second_lit.idx] == None));
            if a.0[first_lit.idx] == None {
                //println!("(first)Assigning in unit_propagate: Lit: {:?}, cref: {:?}", first_lit, cref);
                a.set_assignment(first_lit);
                trail.enq_assignment(first_lit, d, Reason::Long(cref));
            }
            else if a.0[second_lit.idx] == None {
                //println!("(second)Assigning in unit_propagate: Lit: {:?}, cref: {:?}", second_lit, cref);
                f.clauses[cref].0.swap(1, 0);
                a.set_assignment(second_lit);
                trail.enq_assignment(second_lit, d, Reason::Long(cref));
            }
            else {
                //println!("{:?}", lit);
                /*
                while i < trail.trail[d].len() - 1 {
                    trail.trail[d].pop();
                }
                */
                //println!("Returning in unit_propagate: {:?}", cref);
                return Err(cref);
            }
            j += 1;
        }
        i += 1;
    }
    Ok(())
}

enum UnitPropResult {
    False,
    Continue,
    Break,
}


fn inner(f: &mut Formula, a: &mut Assignments, decisionlevel: usize, trail: &mut Trail, watches: &mut Watches) -> bool {
    //watches.check_only_first_two_watched(f, &"TOP OF INNER"); // DEBUG
    let mut dlevel = decisionlevel;
    loop {
        let up_res = match unit_propagate(f, a, dlevel, trail, watches) {
            Ok(_) => { UnitPropResult::Break },
            Err(cref) => {
                // We have a conflict
                if decisionlevel == 0 {
                    return false;
                }
                else {
                    let res = analyze_conflict(f, a, trail, dlevel, cref);
                    match res {
                        Conflict::Ground => {
                            //println!("{:?}", trail.trail);
                            //println!("Ground");
                            return false;
                        },
                        Conflict::Unit(lit) => {
                            //println!("UNIT; LEARNED FACT: {:?}", lit);
                            //println!("{:?}", trail.trail);
                            a.cancel_until(trail, trail.trail.len(), 1); // or is it 0?
                            //trail.trail.push(Vec::new());
                            a.set_assignment(lit);

                            trail.enq_assignment(
                                lit,
                                trail.trail.len()-1,
                                Reason::Unit,
                            );
                            //println!("{:?}", trail.trail);
                            dlevel = trail.trail.len() - 1 ;
                        }
                        Conflict::Learned(level, lit, clause) => {
                            //println!("{:?}", trail.trail);
                            a.cancel_until(trail, trail.trail.len(), level); // +- 1?
                            trail.trail.push(Vec::new());
                            //println!("{:?}", trail.trail);
                            a.set_assignment(lit);
                            let cref = f.add_clause(&Clause(clause), watches);

                            trail.enq_assignment(
                                lit,
                                trail.trail.len()-1, // Is this correct?
                                Reason::Long(cref), // Unsure
                            );
                            dlevel = trail.trail.len() - 1;
                        }
                    }
                UnitPropResult::Continue
                }
            },
        };
        match up_res {
            UnitPropResult::Continue => {}
            UnitPropResult::False => {
                return false;
            }
            UnitPropResult::Break => {
                break;
            }
        }
    }
    let res = a.find_unassigned();
    if res == None {
        //println!("Doing the check");
        return !f.contains_empty(a);
        return true;
    } else {
        let unassigned_idx = res.unwrap();
        //println!("Assigning in inner: {:?}", unassigned_idx);
        trail.trail.push(Vec::new());
        let lit = Lit { idx: unassigned_idx, polarity: false };
        a.set_assignment(lit);
        trail.enq_assignment(
            lit,
            dlevel+1,
            Reason::Decision,
        );
        if inner(f, a, dlevel+1, trail, watches) {
            return true;
        }
        else {
            a.cancel_until(trail, trail.trail.len(), dlevel+1);
            // The assignment may have become a learned unit clause(a fact), so we have to check whether it is assigned after backtracking
            if a.0[unassigned_idx] == None {
                //println!("Second assignment in inner: {:?}", unassigned_idx);
                //println!("Trail is now {:?}", trail.trail);
                trail.trail.push(Vec::new());
                let lit = Lit { idx: unassigned_idx, polarity: true };
                a.set_assignment(lit);
                trail.enq_assignment(
                    lit,
                    trail.trail.len()-1,
                    Reason::Decision,
                );
            }
            return inner(f, a, trail.trail.len()-1, trail, watches);
        }
    }
}

pub fn solver(f: &mut Formula) -> bool {
    if f.num_vars == 0 {
        return true;
    }
    let mut watches = Watches::new(f.num_vars);
    watches.init_watches(f);
    inner(f, &mut Assignments::init_assignments(f), 0, &mut Trail::new(f.num_vars), &mut watches)
}
