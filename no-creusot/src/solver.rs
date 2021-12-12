#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Lit {
    idx: usize,
    polarity: bool,
}

impl Lit {
    // Gets the index of the literal in the representation used for the watchlist
    pub fn to_watchidx(&self) -> usize {
        self.idx * 2 + if self.polarity { 0 } else { 1 }
    }
    // Gets the index of the literal of the opposite polarity(-self) in the representation used for the watchlist
    pub fn to_neg_watchidx(&self) -> usize {
        self.idx * 2 + if self.polarity { 1 } else { 0 }
    }
    pub fn is_sat(&self, assignment: &Assignments) -> bool {
        match assignment.0[self.idx] {
            Some(val) => val == self.polarity,
            None => false,
        }
    }
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
    Uno(Lit),
    Unit(Lit),
}

// I need to figure out a way to actually encode these in a reasonable way within the Rust type system.
// Varisat implements the watchers inside the Clauses with a ClauseRef, which is a struct containing u32 which is used for indexing
struct WatcherO<'a> {
    cref : &'a Clause,
    // blocker : Lit,
}

// Watches is indexed on lit.idx due to hashmaps not being available in Creusot
// Should really take into account polarity somehow, that will be a TODO for now
// Watches[lit.idx] -> Vec<Watcher> where each watcher watches a clause that contains the literal
struct WatchesO<'a> {
    watches: Vec<Vec<&'a WatcherO<'a>>>,
}

// Lets try this scheme and see how well it fares
// Watches are indexed on 2 * lit.idx for positive and 2 * lit.idx + 1 for negative
#[derive(Debug, Default)]
struct Watcher {
    cref: usize,
    //blocker: Lit,
}

#[derive(Debug, Default)]
struct Watches {
    watches: Vec<Vec<Watcher>>,
}

impl Watches {
    // The way clauses are made and added should really be changed - builder pattern?
    pub fn new(num_vars: usize) -> Watches {
        let mut i = 0;
        let mut watches = Vec::new();
        while i < num_vars {
            watches.push(Vec::new());
            watches.push(Vec::new());
            i += 1;
        }
        Watches {watches}
    }

    // We watch the negated literal for updates
    pub fn add_watcher(&mut self, lit: Lit, cref: usize) {
        self.watches[lit.to_neg_watchidx()].push(Watcher {cref});
    }

    // This requires the literal to be watched, otherwise it will panic
    // This method should be updated as we usually know where to look
    pub fn update_watch(&mut self, old_lit: Lit, new_lit: Lit, cref: usize) {
        //assert!(old_lit != new_lit);
        let mut i = 0;
        let old_idx = old_lit.to_watchidx();
        while i < self.watches[old_idx].len() {
            if self.watches[old_idx][i].cref == cref {
                break;
            }
            i += 1;
        }
        //assert!(self.watches[old_idx][i].cref == cref);

        //self.check_invariant("UPDATE_BEFORE");
        let old = self.watches[old_idx].remove(i);
        self.watches[new_lit.to_neg_watchidx()].push(old);
        //self.check_invariant("UPDATE_AFTER");
    }

    // Debug function that checks that all the watches are for one of the first two literals of each clause
    pub fn check_only_first_two_watched(&self, f: &Formula, s: &str) {
        let mut i = 0;
        while i < self.watches.len() {
            let mut j = 0;
            while j < self.watches[i].len() {
                let cref = self.watches[i][j].cref;
                let lit_idx = i / 2;
                if f.clauses[cref].0[0].idx != lit_idx && f.clauses[cref].0[1].idx != lit_idx {
                    panic!("{}\n
                    There exists a watched literal which is not one of the first two literals in the clause!\n
                    Clause: {:?}\n
                    Index: {}\n", s, f.clauses[cref].0, lit_idx);
                }
                j += 1;
            }
            i += 1;
        }
    }

    // Debug function to check that the watchlist is correct
    // Doesnt check that all are watched or that the watched lits are the first in the clause
    pub fn check_invariant(&self, s: &str) {
        use std::collections::HashMap;
        let mut seen = HashMap::new();
        // Check that each literal only has two watches
        for i in 0..self.watches.len() {
            for j in 0..self.watches[i].len() {
                let cref = self.watches[i][j].cref;
                if seen.contains_key(&cref) {
                    if seen[&cref] > 1 {
                        panic!("{}\nThere exists more than two watched literals for the clause with cref: {:?}", s, cref);
                    }
                    seen.insert(cref, seen[&cref] + 1);
                }
                else { 
                    seen.insert(cref, 1);
                }
            }
        }
        // Check for 2 of the same watched literal for each clause
        for i in 0..self.watches.len() {
            let mut seen = HashMap::new();
            for j in 0..self.watches[i].len() {
                let cref = self.watches[i][j].cref;
                if seen.contains_key(&cref) {
                    panic! ("{}\nThere exists duplicate watching of the same literal for the clause with cref: {:?}", s, cref);
                }
                else { 
                    seen.insert(cref, 1);
                }
            }
        }

        
    }

    // The whole org of things should be better to make sure that len 0 and len 1 never occur, and len 2 should be treated as a special case
    pub fn init_watches(&mut self, f: &Formula) {
        let mut i = 0;
        while i < f.clauses.len() {
            let clause = &f.clauses[i].0;
            if clause.len() == 0 {
                panic!("Empty clause");
            }
            else if clause.len() == 1 {
                panic!("Unit clause");
            }
            let mut j = 0;
            while j < 2 {
                let lit = clause[j];
                self.add_watcher(lit, i);
                j += 1;
            }
            i += 1;
        }
        self.check_invariant(&"INIT"); // Debug assertion
        self.check_only_first_two_watched(f, &"RIGHT AFTER INIT"); // Debug assertion
    }
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

fn check_empty(clause: &Clause, a: &Assignments) -> bool {
    let mut i = 0;
    while i < clause.0.len() {
        let lit = clause.0[i];
        let res = a.0[lit.idx];
        match res {
            Some(x) => {
                // false, false || true, true -> clause is SAT
                if lit.polarity == x {
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
        let clause = &f.clauses[i];
        let res = check_empty(clause, a);
        if res {
            return true;
        }
        i += 1
    }
    return false;
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
                    return SatState::Uno(Lit {idx: lit.idx, polarity: lit.polarity});
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
    //trail.0[decisionlevel].push(l);
}

fn enq_assignment(a: &mut Assignments, l: Lit, decisionlevel: usize, trail: &mut Trail) {
    //a.0[l.idx] = Some(l.polarity);
    trail.0[decisionlevel].push(l);
}

// This got pretty ugly with the `j+=1` and `continue` stuff.
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
        set_assignment(a, lit, d, trail);
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

                    // Okay this is cumbersome. I'll look at making it better later.
                    if lit.idx == first_lit.idx {
                        f.clauses[cref].0.swap(0, k);
                    } else {
                        f.clauses[cref].0.swap(1, k);
                        f.clauses[cref].0.swap(1, 0);
                    }
                    watches.update_watch(lit, curr_lit, cref);
                    //j += 1;
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
                    //j += 1;
                    continue 'outer;
                }
                k += 1;
            }
            // If we have gotten here, the clause is either all false or unit
            //assert!(!(a.0[first_lit.idx] == None && a.0[second_lit.idx] == None));
            if a.0[first_lit.idx] == None {
                enq_assignment(a, first_lit, d, trail);
            }
            else if a.0[second_lit.idx] == None {
                enq_assignment(a, second_lit, d, trail);
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

fn do_unit_propagation(f: &mut Formula, a: &mut Assignments, d: usize, trail: &mut Trail, watches: &mut Watches) -> SatState {
    match unit_propagate(f, a, d, trail, watches) {
        SatState::Unsat => { return SatState::Unsat; },
        SatState::Sat => { return SatState::Sat; },
        _ => {return SatState::Unknown;}}
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

fn cancel_until(a: &mut Assignments, trail: &mut Trail, decisionlevel: usize, level: usize) {
    let mut i: usize = decisionlevel;
    while i > level {
        let decisions = trail.0.pop().unwrap();
        let mut j: usize = 0;
        while j < decisions.len() {
            let lit = decisions[j];
            a.0[lit.idx] = None;
            j += 1;
        }
        i -= 1;
    }
}

fn inner(f: &mut Formula, a: &mut Assignments, d: usize, trail: &mut Trail, watches: &mut Watches) -> bool {
    //watches.check_only_first_two_watched(f, &"TOP OF INNER"); // DEBUG
    match do_unit_propagation(f, a, d, trail, watches) {
        SatState::Unsat => { return false; },
        SatState::Sat => { return true; },
        _ => {},
    }
    let res = find_unassigned(a);
    if res == None {
        if contains_empty(f, a) {
            return false;
        }
        return true;
    } else {
        let unassigned_idx = res.unwrap();
        trail.0.push(Vec::new());
        enq_assignment(a, Lit {
            idx: unassigned_idx,
            polarity: false},
            d+1,
            trail,
        );
        if inner(f, a, d+1, trail, watches) {
            return true;
        }
        else {
            cancel_until(a, trail, trail.0.len(), d+1);
            trail.0.push(Vec::new());
            enq_assignment(a, Lit {
                idx: unassigned_idx,
                polarity: true},
                d+1,
                trail);
            return inner(f, a, d+1, trail, watches);
        }
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
    return solver(&mut formula);
}

pub fn solver(f: &mut Formula) -> bool {
    if f.num_vars == 0 {
        return true;
    }
    let mut assignments = init_assignments(f);
    let mut t_vec = Vec::new();
    t_vec.push(Vec::new());
    let mut watches = Watches::new(f.num_vars);
    watches.init_watches(f);
    inner(f, &mut assignments, 0, &mut Trail(t_vec), &mut watches)
}
