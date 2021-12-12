use crate::assignments::*;
//use crate::clause::*;
use crate::formula::*;
use crate::lit::*;
use crate::trail::*;
use crate::watches::*;

#[allow(dead_code)]
enum SatState {
    Unsat,
    Sat,
    Unknown,
}

// Move unit prop? Dunno where. Is it propagating over the assignments, the formula, or is it its own thing.
// Currently leaning towards assignments, but it might also be its own thing. Ill have to think some more about it.

// Requires all clauses to be at least binary.
fn unit_propagate(f: &mut Formula, a: &mut Assignments, d: usize, trail: &mut Trail, watches: &mut Watches) -> SatState {
    //watches.check_only_first_two_watched(f, &"TOP OF UNIT PROP");
    let mut i = 0;
    while i < trail.0[d].len() {
        //watches.check_only_first_two_watched(f, &"START OF TRAIL LOOP");
        let mut j = 0;
        // Get the enqueued literal
        let lit = trail.0[d][i];
        // Set it as true
        a.set_assignment(lit);
        // Find all the clauses that could have become unit(those that watch for this assignment)
        'outer: while j <  watches.watches[lit.to_watchidx()].len() {
            //watches.check_only_first_two_watched(f, &"TOP OF OUTER");
            let cref = watches.watches[lit.to_watchidx()][j].cref;
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
                    watches.update_watch(lit, curr_lit, cref);
                    continue 'outer;
                }
                k += 1;
            }
            // If we have gotten here, the clause is either all false or unit
            //assert!(!(a.0[first_lit.idx] == None && a.0[second_lit.idx] == None));
            if a.0[first_lit.idx] == None {
                trail.enq_assignment(first_lit, d);
            }
            else if a.0[second_lit.idx] == None {
                trail.enq_assignment(second_lit, d);
            }
            else {
                return SatState::Unsat; // Here we will generate a conflict in the future
            }
            j += 1;
        }
        i += 1;
    }
    return SatState::Unknown;
}

fn inner(f: &mut Formula, a: &mut Assignments, d: usize, trail: &mut Trail, watches: &mut Watches) -> bool {
    //watches.check_only_first_two_watched(f, &"TOP OF INNER"); // DEBUG
    match unit_propagate(f, a, d, trail, watches) {
        SatState::Unsat => { return false; },
        SatState::Sat => { return true; },
        _ => {},
    }
    let res = a.find_unassigned();
    if res == None {
        if f.contains_empty(a) {
            return false;
        }
        return true;
    } else {
        let unassigned_idx = res.unwrap();
        trail.0.push(Vec::new());
        trail.enq_assignment(
            Lit {
            idx: unassigned_idx,
            polarity: false },
            d+1,
        );
        if inner(f, a, d+1, trail, watches) {
            return true;
        }
        else {
            a.cancel_until(trail, trail.0.len(), d+1);
            trail.0.push(Vec::new());
            trail.enq_assignment(
                Lit {
                idx: unassigned_idx,
                polarity: true },
                d+1,
            );
            return inner(f, a, d+1, trail, watches);
        }
    }
}

pub fn solver(f: &mut Formula) -> bool {
    if f.num_vars == 0 {
        return true;
    }
    let mut assignments = Assignments::init_assignments(f);
    let mut t_vec = Vec::new();
    t_vec.push(Vec::new());
    let mut watches = Watches::new(f.num_vars);
    watches.init_watches(f);
    inner(f, &mut assignments, 0, &mut Trail(t_vec), &mut watches)
}
