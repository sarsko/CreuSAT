/*
extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;
*/
/*
use std::ops::Index;
use std::ops::IndexMut;
*/

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

/*
#[trusted]
#[ensures(result === true ==> (l === r))]
#[ensures(result === false ==> (l != r))]
#[ensures(result === (l === r))]
*/
fn eqb(l: bool, r: bool) -> bool {
    l == r
}

fn check_if_unit(c: &Clause, a: &Assignments) -> Option<Lit> {
    let mut i = 0;
    let mut unassigned = 0;
    let mut outlit = None;
    while i < c.0.len() {
        let lit = c.0.index(i);
        let res = a.0.index(lit.idx);
        match res {
            Some(x) => {
                // false, false || true, true -> clause is SAT
                if eqb(lit.polarity, *x) {
                    return None;
                }
            }
            None => {
                if unassigned >= 1 {
                    return None;
                }
                outlit = Some(Lit {
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

/// Checks if the clause is satisfied.
/// `true` means the clause is satisfied.
/// `false` means the clause is unsatisfied(empty clause) or that it contains
/// unassigned variables.
fn check_sat(clause: &Clause, a: &Assignments) -> bool {
    let mut i = 0;
    while i < clause.0.len() {
        let lit = clause.0.index(i);
        let res = a.0.index(lit.idx);
        match res {
            Some(x) => {
                // false, false || true, true -> clause is SAT
                if eqb(lit.polarity, *x) {
                    return true;
                }
            }
            None => {} // continue
        }
        i += 1;
    }
    return false;
}

/// Checks if the clause is empty.
fn check_empty(clause: &Clause, a: &Assignments) -> bool {
    let mut i = 0;
    while i < clause.0.len() {
        let lit = clause.0.index(i);
        let res = a.0.index(lit.idx);
        match res {
            Some(x) => {
                // false, false || true, true -> clause is SAT
                if eqb(lit.polarity, *x) {
                    return false;
                }
            }
            None => {
                return false;
            } // May become SAT
        }
        i += 1;
    }
    return true;
}

fn contains_empty(f: &Formula, a: &Assignments) -> bool {
    let mut i = 0;
    while i < f.clauses.len() {
        let clause = f.clauses.index(i);
        let res = check_empty(clause, a);
        if res {
            return true;
        }
        i += 1
    }
    return false;
}

fn consistent(f: &Formula, a: &Assignments) -> bool {
    let mut i = 0;
    while i < f.clauses.len() {
        let clause = f.clauses.index(i);
        let res = check_sat(clause, a);
        if !res {
            return false;
        }
        i += 1
    }
    return true;
}

fn set_assignment(a: &mut Assignments, l: Lit) {
    *a.0.index_mut(l.idx) = Some(l.polarity);
}

fn add_to_worklist(w: &mut Worklist, a: &mut Assignments, l: Lit) {
    w.0.push(l);
    set_assignment(a, l);
}

// We could jump back if clause is found to be unsat hmm.
fn unit_propagate(f: &Formula, a: &mut Assignments, w: &mut Worklist, l: Lit) {
    let mut i = 0;
    while i < f.clauses.len() {
        let clause = f.clauses.index(i);
        match check_if_unit(clause, a) {
            Some(lit) => {
                add_to_worklist(
                    w,
                    a,
                    Lit {
                        idx: lit.idx,
                        polarity: lit.polarity,
                    },
                );
            }
            None => {}
        }
        i += 1
    }
}

fn do_unit_propagation(f: &Formula, a: &mut Assignments, w: &mut Worklist) {
    while let Some(lit) = w.0.pop() {
        unit_propagate(f, a, w, lit);
    }
}

fn find_unassigned(a: &Assignments) -> Option<usize> {
    let mut i = 0;
    while i < a.0.len() {
        let curr = a.0.index(i);
        match curr {
            Some(x) => {} //continue
            None => {
                return Some(i);
            }
        }
        i += 1;
    }
    None
}

fn inner(f: &Formula, a: &mut Assignments, w: &mut Worklist) -> bool {
    do_unit_propagation(f, a, w);
    if consistent(f, a) {
        return true;
    }
    if contains_empty(f, a) {
        return false;
    }
    let res = find_unassigned(a);
    if res == None {
        // This should not happen
        panic!();
        return false;
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
    //    #[invariant(loop_invariant, 0usize <= i && i < f.num_vars)]
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
    // should do pure literal and identifying unit clauses in preproc
    if f.num_vars == 0 {
        return true;
    }
    let mut assignments = init_assignments(f);
    let mut worklist = init_worklist(f);
    inner(f, &mut assignments, &mut worklist)
}
