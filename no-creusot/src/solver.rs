#[derive(Clone, Copy)]
struct Lit {
    idx: usize,
    polarity: bool,
}
struct Clause(Vec<Lit>);
struct Assignments(Vec<Option<bool>>);
struct Trail(Vec<Vec<Lit>>);
pub struct Formula {
    clauses: Vec<Clause>,
    num_vars: usize,
}
enum SatState {
    Unsat,
    Sat,
    Unknown,
    Unit(Lit),
}

impl Assignments {
    fn clone_assignment_vector(&self, v: &Vec<Option<bool>>) -> Vec<Option<bool>> {
        let mut out = Vec::new();
        let mut i = 0;
        while i < v.len() {
            let curr = v[i];
            out.push(curr.clone());
            i += 1;
        }
        return out;
    }
    fn clone(&self) -> Self {
        Assignments(self.clone_assignment_vector(&self.0))
    }
}


fn check_if_unit(c: &Clause, a: &Assignments) -> SatState {
    let mut i = 0;
    let mut unassigned = 0;
    let mut outlit = SatState::Unsat;
    while i < c.0.len() {
        let lit = c.0[i];
        let res = a.0[lit.idx];
        match res {
            Some(x) => {
                // false, false || true, true -> clause is SAT
                if lit.polarity == x {
                    return SatState::Sat;
                }
            }
            None => {
                if unassigned >= 1 {
                    return SatState::Unknown;
                }
                outlit = SatState::Unit(Lit {
                    idx: lit.idx,
                    polarity: lit.polarity,
                }); // TODO fix
                unassigned += 1;
            }
        }
        i += 1;
    }
    return outlit;
}

fn increase_decision_level(trail: &mut Trail, decisionlevel: &mut usize) {
    *decisionlevel += 1;
    trail.0.push(Vec::new());
}

fn set_assignment(a: &mut Assignments, l: Lit, decisionlevel: usize, trail: &mut Trail) {
    a.0[l.idx] = Some(l.polarity);
    //trail.0.index_mut(decisionlevel).push(l);
}

fn unit_propagate(f: &Formula, a: &mut Assignments, s: &mut bool, d: &mut usize, trail: &mut Trail) -> SatState {
    let mut i = 0;
    let mut out = SatState::Sat;
    while i < f.clauses.len() {
        let clause = &f.clauses[i];
        match check_if_unit(clause, a) {
            SatState::Unit(lit) => {
                set_assignment(a, lit, *d, trail);
                *s = true;
            }
            SatState::Unsat => { return SatState::Unsat; },
            SatState::Unknown => { out = SatState::Unknown; },
            _ => {}
        }
        i += 1
    }
    return out;
}

fn do_unit_propagation(f: &Formula, a: &mut Assignments, d: &mut usize, trail: &mut Trail) -> SatState {
    let mut b = true;
    while b {
        b = false;
        match unit_propagate(f, a, &mut b, d, trail) {
            SatState::Unsat => { return SatState::Unsat; },
            SatState::Sat => { return SatState::Sat; },
            _ => {},
        }
    }
    return SatState::Unknown;
}

fn find_unassigned(a: &Assignments) -> Option<usize> {
    let mut i = 0;
    while i < a.0.len() {
        let curr = a.0[i];
        match curr {
            Some(_x) => {} //continue
            None => {
                return Some(i);
            }
        }
        i += 1;
    }
    None
}

fn cancel_until(a: &mut Assignments, t: &mut Trail, decisionlevel: usize, level: usize) {
    let mut i: usize = decisionlevel;
    while i > level {
        let decisions = t.0.pop().unwrap();
        let mut j: usize = 0;
        while j < decisions.len() {
            let lit = decisions[j];
            a.0[lit.idx] = None;
            j += 1;
        }
        i -= 1;
    }
}

fn inner(f: &Formula, a: &mut Assignments, d: &mut usize, trail: &mut Trail) -> bool {
    match do_unit_propagation(f, a, d, trail) {
        SatState::Unsat => { return false; },
        SatState::Sat => { return true; },
        _ => {},
    }
    let res = find_unassigned(a);
    if res == None {
        // This should not happen
        panic!();
    } else {
        let unassigned_idx = res.unwrap();
        let mut a_cloned = a.clone();
        set_assignment(&mut a_cloned, Lit {
            idx: unassigned_idx,
            polarity: true},
            *d,
            trail,
    );
        set_assignment(a, Lit {
            idx: unassigned_idx,
            polarity: false},
            *d,
            trail,
        );
        return inner(f, a, d, trail) || inner(f, &mut a_cloned, d, trail);
    }
}

fn init_assignments(f: &Formula) -> Assignments {
    let mut assign: Vec<Option<bool>> = Vec::new();
    let mut i = 0;
    while i < f.num_vars {
        assign.push(None);
        i += 1
    }
    Assignments(assign)
}

/// Takes a 1-indexed 2d vector and converts it to a 0-indexed formula
pub fn preproc_and_solve(
    clauses: &mut std::vec::Vec<std::vec::Vec<i32>>,
    num_literals: usize,
) -> bool {
    let mut formula = Formula {
        clauses: Vec::new(),
        num_vars: num_literals,
    };
    for clause in clauses {
        let mut currclause = Clause(Vec::new());
        for lit in clause {
            if *lit < 0 {
                let new_lit = Lit {
                    idx: ((lit.abs() - 1) as usize),
                    polarity: false,
                };
                currclause.0.push(new_lit);
            } else {
                let new_lit = Lit {
                    idx: ((*lit - 1) as usize),
                    polarity: true,
                };
                currclause.0.push(new_lit);
            }
        }
        formula.clauses.push(currclause);
    }
    return solver(&formula);
}

pub fn solver(f: &Formula) -> bool {
    if f.num_vars == 0 {
        return true;
    }
    let mut assignments = init_assignments(f);
    inner(f, &mut assignments, &mut 0, &mut Trail(Vec::new()))
}
