extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

pub struct Ghost<T>(*mut T)
where
    T: ?Sized;

impl<T> Model for Ghost<T> {
    type ModelTy = T;
    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        panic!()
    }
}

impl<T> Ghost<T> {
    #[trusted]
    #[ensures(@result === *a)]
    fn record(a: &T) -> Ghost<T> {
        panic!()
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

fn main() {}

impl Worklist {
    // OK(safety)
    #[trusted]
    fn clone_lit_vector(&self, v: &Vec<Lit>) -> Vec<Lit> {
        let mut out = Vec::new();
        let mut i = 0;
        #[invariant(loop_invariant, 0usize <= i && @i <= (@v).len())]
        while i < v.len() {
            let lit = &v[i];
            let newlit = Lit {
                idx: lit.idx,
                polarity: lit.polarity,
            };
            out.push(newlit);
            i += 1;
        }
        return out;
    }
    #[trusted]
    fn clone(&self) -> Self {
        Worklist(self.clone_lit_vector(&self.0))
    }
}
impl Assignments {
    //Lacking pre for .clone()
    #[trusted]
    fn clone_assignment_vector(&self, v: &Vec<Option<bool>>) -> Vec<Option<bool>> {
        let mut out = Vec::new();
        let mut i = 0;
        #[invariant(loop_invariant, 0usize <= i && @i <= (@v).len())]
        while i < v.len() {
            let curr = v[i];
            out.push(curr.clone());
            i += 1;
        }
        return out;
    }
    #[trusted]
    fn clone(&self) -> Self {
        Assignments(self.clone_assignment_vector(&self.0))
    }
}

#[trusted]
#[ensures(result === true ==> (l === r))]
#[ensures(result === false ==> (l != r))]
#[ensures(result === (l === r))]
fn eqb(l: bool, r: bool) -> bool {
    l == r
}

#[trusted] // TODO REMOVE ME
#[requires(idx < f.num_vars)]
#[requires(assignments_invariant(*f, *a))]
fn check_if_unit(f: &Formula, idx: usize, a: &Assignments) -> Option<Lit> {
    let c = &f.clauses[idx];
    let mut i = 0;
    let mut unassigned = 0;
    let mut outlit = None;
    #[invariant(loop_invariant, 0usize <= i && @i <= (@c.0).len())]
    while i < c.0.len() {
        let lit = c.0[i];
        let res = a.0[lit.idx];
        match res {
            Some(x) => {
                // false, false || true, true -> clause is SAT
                if eqb(lit.polarity, x) {
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

// OK(safety)
/// Checks if the clause is satisfied.
/// `true` means the clause is satisfied.
/// `false` means the clause is unsatisfied(empty clause) or that it contains
/// unassigned variables.
#[requires(@idx < (@f.clauses).len())]
#[requires(assignments_invariant(*f, *a))]
#[requires(formula_invariant(*f))]
fn check_sat(f: &Formula, idx: usize, a: &Assignments) -> bool {
    let clause = &f.clauses[idx];
    let mut i = 0;
    #[invariant(loop_invariant, 0usize <= i && @i <= (@clause.0).len())]
    while i < clause.0.len() {
        let lit = clause.0[i];
        let res = a.0[lit.idx];
        match res {
            Some(x) => {
                // false, false || true, true -> clause is SAT
                if eqb(lit.polarity, x) {
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
#[requires(@idx < (@f.clauses).len())]
#[requires(assignments_invariant(*f, *a))]
#[requires(formula_invariant(*f))]
fn check_empty(f: &Formula, idx: usize, a: &Assignments) -> bool {
    let clause = &f.clauses[idx];
    let mut i = 0;
    #[invariant(loop_invariant, 0usize <= i && @i <= (@clause.0).len())]
    while i < clause.0.len() {
        let lit = clause.0[i];
        let res = a.0[lit.idx];
        match res {
            Some(x) => {
                // false, false || true, true -> clause is SAT
                if eqb(lit.polarity, x) {
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

#[requires(assignments_invariant(*f, *a))]
#[requires(formula_invariant(*f))]
fn contains_empty(f: &Formula, a: &Assignments) -> bool {
    let mut i = 0;
    #[invariant(loop_invariant, 0usize <= i && @i <= (@f.clauses).len())]
    while i < f.clauses.len() {
        let mut j = 0;
        let mut ret = true;
        let clause = &f.clauses[i];
        #[invariant(loop_invariant2, 0usize <= j && @j <= (@clause.0).len())]
        while j < clause.0.len() {
            let lit = clause.0[j];
            let res = a.0[lit.idx];
            match res {
                Some(x) => {
                    // false, false || true, true -> clause is SAT
                    if eqb(lit.polarity, x) {
                        ret = false;
                        break;
                    }
                }
                None => {
                    ret = false;
                    break;
                } // May become SAT
            }
            j += 1;
        }
        if ret {
            return true;
        }
        i += 1
    }
    return false;
}

#[requires(assignments_invariant(*f, *a))]
#[requires(formula_invariant(*f))]
fn consistent(f: &Formula, a: &Assignments) -> bool {
    let mut i = 0;
    #[invariant(loop_invariant, 0usize <= i && @i <= (@f.clauses).len())]
    while i < f.clauses.len() {
        let mut j = 0;
        let mut ret = false;
        let clause = &f.clauses[i];
        #[invariant(loop_invariant2, 0usize <= j && @j <= (@clause.0).len())]
        while j < clause.0.len() {
            let lit = clause.0[j];
            let res = a.0[lit.idx];
            match res {
                Some(x) => {
                    // false, false || true, true -> clause is SAT
                    if eqb(lit.polarity, x) {
                        ret =  true;
                        break;
                    }
                }
                None => {} // continue
            }
            j += 1;
        }
        if !ret {
            return false;
        }
        i += 1
    }
    return true;
}

#[requires(assignments_invariant(*_f, *a))]
#[ensures(assignments_invariant(*_f, ^a))]
//#[requires(worklist_invariant(*w, *a))]
//#[ensures(worklist_invariant(^w, ^a))]
#[requires(@idx < (@a.0).len())]
#[ensures(@idx < (@a.0).len())]
#[requires(formula_invariant(*_f))]
fn add_to_worklist(_f: &Formula, w: &mut Worklist, a: &mut Assignments, idx: usize, polarity: bool) {
    w.0.push(Lit{idx: idx, polarity: polarity});
    a.0[idx] = Some(polarity);
}

// We could jump back if clause is found to be unsat hmm.

#[trusted] // TODO REMOVE ME
#[requires(assignments_invariant(*f, *a))]
#[ensures(assignments_invariant(*f, ^a))]
//#[requires(worklist_invariant(*w, *a))]
//#[ensures(worklist_invariant(^w, ^a))]
#[requires(formula_invariant(*f))]
fn unit_propagate(f: &Formula, a: &mut Assignments, w: &mut Worklist, l: Lit) {
    let mut i = 0;
    #[invariant(loop_invariant, 0usize <= i && @i <= (@f.clauses).len())]
    while i < f.clauses.len() {
        match check_if_unit(f, i, a) {
            Some(lit) => {
                add_to_worklist(
                    f,
                    w,
                    a,
                    lit.idx,
                    lit.polarity,
                );
            }
            None => {}
        }
        i += 1
    }
}

#[trusted] // TODO REMOVE ME
#[requires(assignments_invariant(*f, *a))]
#[ensures(assignments_invariant(*f, ^a))]
//#[requires(worklist_invariant(*w, *a))]
//#[ensures(worklist_invariant(^w, ^a))]
#[requires(formula_invariant(*f))]
fn do_unit_propagation(f: &Formula, a: &mut Assignments, w: &mut Worklist) {
    #[invariant(ass, assignments_invariant(*f, *a))]
    #[invariant(wl, worklist_invariant(*w, *a))]
    while let Some(lit) = w.0.pop() {
        unit_propagate(f, a, w, lit);
    }
}

// OK(safety)
fn find_unassigned(a: &Assignments) -> Option<usize> {
    let mut i = 0;
    #[invariant(loop_invariant, 0usize <= i && @i <= (@a.0).len())]
    while i < a.0.len() {
        let curr = a.0[i];
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


#[requires(assignments_invariant(*f, *a))]
#[ensures(assignments_invariant(*f, ^a))]
//#[requires(worklist_invariant(*w, *a))]
//#[ensures(worklist_invariant(^w, ^a))]
#[requires(formula_invariant(*f))]
fn inner(f: &Formula, a: &mut Assignments, w: &mut Worklist) -> bool {
//    do_unit_propagation(f, a, w);
    if consistent(f, a) {
        return true;
    }
    if contains_empty(f, a) {
        return false;
    }
    let res = find_unassigned(a);
    let ex:Option<bool> = None;
    let none = None;
    if ex == none {
    }
    match res {
        None => {
            // This should not happen
            return false;
        }
        Some(x) => {
            let unassigned_idx = res.unwrap();
            let mut a_cloned = a.clone();
            let mut w_cloned = w.clone();
            add_to_worklist(
                f,
                w,
                a,
                unassigned_idx,
                true,
            );
            add_to_worklist(
                f,
                &mut w_cloned,
                &mut a_cloned,
                unassigned_idx,
                false,
            );
            return inner(f, a, w) || inner(f, &mut a_cloned, &mut w_cloned);
        }
    }
}

#[predicate]
fn vars_in_range(n: Int, c: Clause) -> bool {
    pearlite! {
        forall<i: usize> 0usize <= i && @i < (@(c.0)).len() ==>
            (0 <= @((@(c.0))[@i]).idx &&
        @((@(c.0))[@i]).idx < n)
    }
}

#[predicate]
fn formula_invariant(f: Formula) -> bool {
    pearlite! {
        (forall<i: usize> 0usize <= i && @i < (@(f.clauses)).len() ==>
        vars_in_range(@(f.num_vars), ((@(f.clauses))[@i])))
    }
}

#[predicate]
fn assignments_invariant(f: Formula, a: Assignments) -> bool {
    pearlite! {
        @f.num_vars === (@a.0).len()
    }
}

#[predicate]
fn worklist_invariant(w: Worklist, a: Assignments) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < (@w.0).len() ==>
            @((@w.0)[i].idx) < (@a.0).len()
    }
}

// OK(safety)
#[ensures(assignments_invariant(*f, result))]
#[requires(formula_invariant(*f))]
fn init_assignments(f: &Formula) -> Assignments {
    let mut assign: Vec<Option<bool>> = Vec::new();
    let mut i = 0;
    #[invariant(loop_invariant, 0usize <= i && i <= f.num_vars)]
    #[invariant(length_invariant, (@assign).len() === @i)]
    while i < f.num_vars {
        assign.push(None);
        i += 1
    }
    Assignments(assign)
}

// OK(safety)
#[ensures((@result.0).len() === 0)]
#[ensures(worklist_invariant(result, *_a))]
#[requires(formula_invariant(*_f))]
fn init_worklist(_f: &Formula, _a: &Assignments) -> Worklist {
    let litvec: Vec<Lit> = Vec::new();
    Worklist(litvec)
}

/// Takes a 1-indexed 2d vector and converts it to a 0-indexed formula
#[trusted]
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

#[requires((@(f.clauses)).len() < 10000)] // just to ensure boundedness
#[requires(formula_invariant(*f))]
pub fn solver(f: &Formula) -> bool {
    // should do pure literal and identifying unit clauses in preproc
    if f.num_vars == 0 {
        return true;
    }
    let mut assignments = init_assignments(f);
    let mut worklist = init_worklist(f, &assignments);
    inner(f, &mut assignments, &mut worklist)
}
