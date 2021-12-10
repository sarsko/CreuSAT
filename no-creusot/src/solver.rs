pub struct Vec<T>(std::vec::Vec<T>);
impl<T> Vec<T> {
    pub fn new() -> Self {
        Vec(std::vec::Vec::new())
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn get(&self, ix: usize) -> Option<&T> {
        self.0.get(ix)
    }

    pub fn push(&mut self, v: T) {
        self.0.push(v)
    }

    pub fn index(&self, ix: usize) -> &T {
        use std::ops::Index;
        self.0.index(ix)
    }

    pub fn index_mut(&mut self, ix: usize) -> &mut T {
        use std::ops::IndexMut;
        self.0.index_mut(ix)
    }

    pub fn swap(&mut self, i: usize, j: usize) {
        self.0.swap(i, j)
    }

    pub fn pop(&mut self) -> Option<T> {
        self.0.pop()
    }
}

#[derive(Clone, Copy)]
struct Lit {
    idx: usize,
    polarity: bool,
}
struct Clause(Vec<Lit>);
struct Assignments(Vec<Option<bool>>);
struct Worklist(Vec<Lit>);
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

impl Worklist {
    fn clone_lit_vector(&self, v: &Vec<Lit>) -> Vec<Lit> {
        let mut out = Vec::new();
        let mut i = 0;
        while i < v.len() {
            let lit = v.index(i);
            let newlit = Lit {
                idx: lit.idx,
                polarity: lit.polarity,
            };
            out.push(newlit);
            i += 1;
        }
        return out;
    }
    fn clone(&self) -> Self {
        Worklist(self.clone_lit_vector(&self.0))
    }
}

impl Assignments {
    fn clone_assignment_vector(&self, v: &Vec<Option<bool>>) -> Vec<Option<bool>> {
        let mut out = Vec::new();
        let mut i = 0;
        while i < v.len() {
            let curr = v.index(i);
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
        let lit = c.0.index(i);
        let res = a.0.index(lit.idx);
        match res {
            Some(x) => {
                // false, false || true, true -> clause is SAT
                if lit.polarity == *x {
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

fn set_assignment(a: &mut Assignments, l: Lit) {
    *a.0.index_mut(l.idx) = Some(l.polarity);
}

fn add_to_worklist(w: &mut Worklist, a: &mut Assignments, l: Lit) {
    w.0.push(l);
    set_assignment(a, l);
}

fn unit_propagate(f: &Formula, a: &mut Assignments, s: &mut Worklist,) -> SatState {
    let mut i = 0;
    let mut out = SatState::Sat;
    while i < f.clauses.len() {
        let clause = f.clauses.index(i);
        match check_if_unit(clause, a) {
            SatState::Unit(lit) => {
                add_to_worklist(
                    s,
                    a,
                    Lit {
                        idx: lit.idx,
                        polarity: lit.polarity,
                    },
                );
            }
            SatState::Unsat => { return SatState::Unsat; },
            SatState::Unknown => { out = SatState::Unknown; },
            _ => {}
        }
        i += 1
    }
    return out;
}

fn do_unit_propagation(f: &Formula, a: &mut Assignments, w: &mut Worklist) -> SatState {
    while let Some(_lit) = w.0.pop() {
        match unit_propagate(f, a, w) {
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
        let curr = a.0.index(i);
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

fn inner(f: &Formula, a: &mut Assignments, w: &mut Worklist) -> bool {
    match do_unit_propagation(f, a, w) {
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
        let mut w_cloned = w.clone();
        add_to_worklist(
            w,
            a,
            Lit {
                idx: unassigned_idx,
                polarity: true,
            },
        );
        add_to_worklist(
            &mut w_cloned,
            &mut a_cloned,
            Lit {
                idx: unassigned_idx,
                polarity: false,
            },
        );
        return inner(f, a, w) || inner(f, &mut a_cloned, &mut w_cloned);
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

fn init_worklist(_f: &Formula) -> Worklist {
    let litvec: Vec<Lit> = Vec::new();
    Worklist(litvec)
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
    let mut worklist = init_worklist(f);
    inner(f, &mut assignments, &mut worklist)
}
