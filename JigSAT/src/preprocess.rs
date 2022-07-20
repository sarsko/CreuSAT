// This is the simplification / preprocessing engine for JigSAT.
// It is based on the SimpSolver of Glucose/MiniSat

// Instead of being a full solver which extends the internal solver,
// it is merely a helper struct. The reason for this is that I do
// not want the SimpSolver to be callable directly

use log::debug;
use std::collections::VecDeque;
//use std::collections::BinaryHeap;

use crate::{decision::*, formula::*, lit::*, solver_types::*, trail::*, unit_prop::unit_propagate, watches::*};

#[derive(PartialEq)]
pub(crate) enum SubsumptionRes {
    NoSubsumption,
    Subsumed,
    RemoveLit(Lit),
}
/*

pub(crate) struct Preprocess {
    touched: Vec<bool>,
    occurs: Vec<Vec<Cref>>, /* From watch_index to a vec of crefs where the variable occurs */
    // OccLists<Var, vec<Cref>, ClauseDeleted>,
    n_occ: Vec<usize>, //
    // elim_heap: Heap, // A heap to remove the minimal element efficiently. We could either use a heap, or be lazy and use a vector.
    elim_heap: Vec<(usize, usize)>, // Vars and their number of occurrences. is sorted decending on k.1
    //elim_heap: BinaryHeap<Var>,
    subsumption_queue: VecDeque<Cref>, // A vector of crefs to visit
    eliminated: Vec<bool>,

    bwdsub_assigns: usize,
    n_touched: usize,

    // Options
    grow: usize,
    clause_lim: usize, // MiniSat/Glucose uses -1 as a magic number for no limit. We just use usize::MAX, as they are in practice equivalent.
    subsumption_lim: usize, // Same applies to this.

    merges: usize,
    eliminated_vars: usize,
}

impl Preprocess {
    // Init needs to be called later.
    pub(crate) fn new() -> Preprocess {
        Preprocess {
            touched: Vec::new(),
            occurs: Vec::new(),
            n_occ: Vec::new(),
            elim_heap: Vec::new(),
            subsumption_queue: VecDeque::new(),
            eliminated: Vec::new(),
            bwdsub_assigns: 0,
            n_touched: 0,
            grow: 0,
            clause_lim: 20,
            subsumption_lim: 1000,
            merges: 0,
            eliminated_vars: 0,
        }
    }

    // Requires empty elim heap
    fn populate_elim(&mut self) {
        let mut j = 0;
        for i in (0..self.n_occ.len()).step_by(2) {
            self.elim_heap.push((j, self.n_occ[i] * self.n_occ[i + 1]));
            j += 1;
        }
        self.elim_heap.sort_by_key(|k| k.1);
        self.elim_heap.reverse();
    }

    fn populate_occurs_and_n_occ(&mut self, formula: &ClauseArena) {
        self.occurs = vec![Vec::new(); formula.num_vars() * 2];
        self.n_occ = vec![0; formula.num_vars() * 2];
        //for (i, c) in formula.iter().enumerate() {
        let mut i = 0;
        let mut j = 0;
        while j < formula.len() {
            let c = &formula[j];
            for l in c.get_literals() {
                self.occurs[l.index()].push(i);
                self.n_occ[l.to_watchidx()] += 1;
            }
            i += 1;
            j += 1;
        }
    }

    fn populate_subsumption_queue(&mut self, formula: &ClauseArena) {
        // Populated as part of gather_touched_clauses
        // unimplemented!()
    }

    fn init(&mut self, formula: &ClauseArena) {
        self.touched = vec![false; formula.num_vars()];
        self.populate_occurs_and_n_occ(formula);
        self.populate_elim();
        self.populate_subsumption_queue(formula);
        self.eliminated = vec![false; formula.num_vars()];
    }
}

impl Preprocess {
    fn add_clause(&mut self, formula: &mut ClauseArena, lits: Vec<Lit>) -> bool {
        debug!("Adding: {:?}", &lits);
        let clause = Clause::new(lits);
        let cref = formula.add_unwatched_clause(clause);
        debug!("Added: {}", cref);
        self.subsumption_queue.push_back(cref);
        for l in formula[cref].get_literals() {
            self.occurs[l.index()].push(cref);
            self.n_occ[l.to_watchidx()] += 1;
            self.touched[l.index()] = true;
            self.n_touched += 1;
            //if(elim_heap.inHeap(var(c[i]))) elim_heap.increase(var(c[i]));
        }
        true // We should check for trivially UNSAT
    }

    fn gather_touched_clauses(&mut self, formula: &mut ClauseArena) {
        if self.n_touched == 0 {
            return;
        }

        for e in &self.subsumption_queue {
            if formula[*e].get_mark() == 0 {
                formula[*e].set_mark(2);
            }
        }

        for i in 0..self.touched.len() {
            if self.touched[i] {
                let cs = &mut self.occurs[i];
                let mut j = 0;
                //for j in 0..cs.len() {
                //if formula[cs[j]].get_mark() == 0 && !formula[cs[j]].deleted {
                while j < cs.len() {
                    if !formula[cs[j]].is_deleted() {
                        cs.swap_remove(j);
                    } else if formula[cs[j]].get_mark() == 0 {
                        self.subsumption_queue.push_back(cs[j]);
                        formula[cs[j]].set_mark(2);
                        j += 1;
                    }
                }
                self.touched[i] = false;
            }
        }

        for e in &self.subsumption_queue {
            if formula[*e].get_mark() == 2 {
                formula[*e].set_mark(0);
            }
        }

        self.n_touched = 0;
    }

    // Corresponds to SimpSolver::eliminate in Glucose
    // Glucose passes turn_off_elim as true, which means that it always cleans up fully afterwards
    // We just pass Preprocess as `mut self`, to have it drop at function exit
    pub(crate) fn preprocess(
        mut self, formula: &mut ClauseArena, trail: &mut Trail, decisions: &mut impl Decisions, watches: &mut Watches,
    ) -> bool {
        self.init(formula);

        // This should be uncommented.
        /*
        if !self.simplify() {
            return false;
        }
        */
        if formula.len() >= 50000000 {
            println!("c Too many clauses. No preprocessing.");
            return false;
        }

        while self.n_touched > 0 || self.bwdsub_assigns < trail.trail.len() || self.elim_heap.len() > 0 {
            self.gather_touched_clauses(formula);

            if self.subsumption_queue.len() > 0 || self.bwdsub_assigns < trail.trail.len() {
                match self.backward_subsumption_check(formula, trail, watches) {
                    Some(false) => return false,
                    Some(true) => {}
                    None => break,
                }
            }

            while !self.elim_heap.is_empty() {
                let (elim, _) = self.elim_heap.pop().unwrap();

                if self.eliminated[elim] || trail.assignments.is_assigned(elim) {
                    continue;
                }

                // We dont do assym

                // We always do elim (and therefore dont have to check if has become set by assym)
                // !frozen[elim] &&  // We dont support frozen vars (only for assumptions -> we are not incremental)
                match self.eliminate_var(elim, formula, trail, watches) {
                    Some(false) => return false,
                    Some(true) => {}
                    None => break,
                }
            }
        }
        for (idx, val) in self.eliminated.iter().enumerate() {
            if *val {
                decisions.turn_off_decision_for_idx(idx);
            }
        }
        formula.remove_deleted();

        *watches = Watches::new(formula);
        watches.init_watches(formula);

        true
    }

    fn remove_clause_in_preprocessing(&mut self, formula: &mut ClauseArena, cref: usize) {
        if formula[cref].is_deleted() {
            unreachable!("Already deleted");
            return;
        }
        debug!("Removing cref: {}, {:?}", cref, formula[cref].get_literals());
        for l in formula[cref].get_literals() {
            self.n_occ[l.to_watchidx()] -= 1;
            if let Some(index) = self.occurs[l.index()].iter().position(|value| *value == cref) {
                debug!("Removed clause {} due to {}", &formula[cref], l);
                debug!("Cref: {} index: {}, cref at index: {}", cref, index, self.occurs[l.index()][index]);
                self.occurs[l.index()].swap_remove(index);
            } else {
                // Can happen if var is removed.
                unreachable!("{:?} not found in occurs: {:?}", l, self.occurs[l.index()]);
            }
        }
        formula.mark_clause_as_deleted(cref);
    }

    // Backward subsumption + backward subsumption resolution
    //bool SimpSolver::backwardSubsumptionCheck(bool v) {
    fn backward_subsumption_check(
        &mut self, formula: &mut ClauseArena, trail: &mut Trail, watches: &mut Watches,
    ) -> Option<bool> {
        //assert(decisionLevel() == 0);

        while self.subsumption_queue.len() > 0 || self.bwdsub_assigns < trail.trail.len() {
            // Check top-level assignments by creating a dummy clause and placing it in the queue:
            if self.subsumption_queue.len() == 0 && self.bwdsub_assigns < trail.trail.len() {
                println!("c sub_q.len() == 0 and bwdsub_assigns < trail.len()");
                //panic!();
                return None;
                // I dunno what is supposed to happen here.
                // If we are not done somehow, then add a dummy clause consisting of the lit
                // on the current index of the trail, and then enqueue that. Why?
                /*
                let l = trail.trail[self.bwdsub_assigns].lit;
                self.bwdsub_assigns += 1;
                ca[bwdsub_tmpunit][0] = l;
                ca[bwdsub_tmpunit].calcAbstraction();
                self.subsumption_queue.push(bwdsub_tmpunit);
                */
            }

            let cr = self.subsumption_queue.pop_front().unwrap();
            //let c = &formula[cr];

            // When is the clause marked?
            if formula[cr].is_marked() || formula[cr].is_deleted() {
                continue;
            }

            //assert(c.size() > 1 || value(c[0]) == l_True);   // Unit-clauses should have been propagated before this point.

            // Find best variable to scan:
            let mut best = formula[cr][0].index();
            for i in 1..formula[cr].len() {
                if self.occurs[formula[cr][i].index()].len() < self.occurs[best].len() {
                    best = formula[cr][i].index();
                }
            }

            // WATCH OUT! Error prone handling of j !!
            let mut j = 0;
            while j < self.occurs[best].len() {
                // How can c become marked since the previous check?
                if formula[cr].is_marked() {
                    break;
                } else if !formula[self.occurs[best][j]].is_marked()
                    && self.occurs[best][j] != cr
                    && formula[self.occurs[best][j]].len() < self.subsumption_lim
                {
                    match formula[cr].subsumes(&formula[self.occurs[best][j]]) {
                        SubsumptionRes::NoSubsumption => {
                            j += 1;
                        }
                        SubsumptionRes::Subsumed => {
                            //println!("Subsumed");
                            //subsumed += 1;
                            self.remove_clause_in_preprocessing(formula, self.occurs[best][j]);
                            j += 1;
                        }
                        SubsumptionRes::RemoveLit(l) => {
                            //println!("Removed");
                            //deleted_literals += 1;

                            if !self.strengthen_clause(self.occurs[best][j], !l, formula, trail, watches) {
                                return Some(false);
                            }

                            // Did current candidate get deleted from cs? Then check candidate at index j again:
                            if l.index() == best {
                                //println!("c Best");
                            } else {
                                j += 1;
                            }
                        }
                    }
                } else {
                    j += 1;
                }
            }
        }

        Some(true)
    }

    // What happens if we ever try to strengthen a unit?
    // I would not be surprised if we are unsound, and have to init watches + do unit prop both beforehand and during preprocessing.
    fn strengthen_clause(
        &mut self, cref: usize, lit: Lit, formula: &mut ClauseArena, trail: &mut Trail, watches: &mut Watches,
    ) -> bool {
        let c = &mut formula[cref];
        //assert(decisionLevel() == 0);

        // FIX: this is too inefficient but would be nice to have (properly implemented)
        // if (!find(subsumption_queue, &c))
        // I don't get this call in general, especially not in the case the clause becomes unit ?
        self.subsumption_queue.push_back(cref);

        // I suspect we will fail on units
        /*
        if c.len() == 1 {
            panic!();
        }
        */

        if c.len() == 2 {
            c.strengthen(lit);
            let unit_lit = c[0];
            formula.mark_clause_as_deleted(cref);
            trail.learn_unit_in_preprocessing(unit_lit, formula);
            let mut mock = 0;
            return match unit_propagate(formula, trail, watches, &mut mock) {
                Err(_) => false,
                _ => true,
            };

            // return enqueue(c[0]) && propagate() == CRef_Undef
        } else {
            //self.subsumption_queue.push_back(cref);
            // No need to detach + attach: we are not watched, and do not use a clause arena.
            //detachClause(cr, true);
            c.strengthen(lit);
            //attachClause(cr);
            // Remove this cref from occurs
            if let Some(index) = self.occurs[lit.index()].iter().position(|value| *value == cref) {
                self.occurs[lit.index()].swap_remove(index);
            }
            self.n_occ[lit.to_watchidx()] -= 1;
            // TODO: Update the elim_heap
            //updateElimHeap(var(l));
        }
        true
    }

    // v is the index of the var to be removed
    fn eliminate_var(
        &mut self, v: usize, formula: &mut ClauseArena, trail: &mut Trail, watches: &mut Watches,
    ) -> Option<bool> {
        /*
        assert(!frozen[v]);
        assert(!isEliminated(v));
        assert(value(v) == l_Undef);
        */

        // Split the occurrences into positive and negative:
        //
        let mut pos = Vec::new();
        let mut neg = Vec::new();
        for e in &self.occurs[v] {
            if Lit::new(v, true).lit_in_clause(&formula[*e].get_literals()) {
                pos.push(*e);
            } else if Lit::new(v, false).lit_in_clause(&formula[*e].get_literals()) {
                neg.push(*e);
            } else {
                panic!("Haha");
            }
        }

        let mut cnt = 0;
        let mut clause_size = 0;

        for i in 0..pos.len() {
            for j in 0..neg.len() {
                cnt += 1;
                if self.merge(&formula[pos[i]], &formula[neg[j]], v, &mut clause_size)
                    && (cnt > self.occurs[v].len() + self.grow || clause_size > self.clause_lim)
                {
                    return Some(true);
                }
            }
        }

        debug!("Eliminated: {}", v);
        // Delete and store old clauses:
        self.eliminated[v] = true;
        // TODO: Actually reduce the var count
        //setDecisionVar(v, false);
        self.eliminated_vars += 1;

        /*
        // TODO: Handling this is needed to output the correct model
        if pos.len() > neg.len() {
            //for(int i = 0; i < neg.size(); i++) {
            for e in neg {
                mkElimClause(elimclauses, v, formula[e]);
            }
            mkElimClause(elimclauses, mkLit(v));
        } else {
            //for(int i = 0; i < pos.size(); i++) {
            for e in pos {
                mkElimClause(elimclauses, v, formula[e]);
            }
            mkElimClause(elimclauses, ~mkLit(v));
        }
        */

        // Make all possible resolvents (AKA DP)
        for p in &pos {
            for n in &neg {
                let mut resolvent = Vec::new();
                if formula[*p].is_deleted() || formula[*n].is_deleted() {
                    panic!("Deleted clauses used in the DP procedure");
                    continue;
                }
                if self.merge_and_get(&formula[*p], &formula[*n], v, &mut resolvent) {
                    debug!("Resolved {} and {} to get {:?}", &formula[*p], &formula[*n], &resolvent);

                    if !self.add_clause(formula, resolvent) {
                        return Some(false);
                    }
                }
            }
        }

        // The literal is removed -> remove all the clauses which contains it.
        // (we just mark them as deleted to not mess up the rest of the data structures.
        self.remove_clauses(formula, v);

        // Occurs is wiped in remove_clauses as well
        assert!(self.occurs[v].len() == 0);

        // (We do this before adding watches, so there are no watchers to clear)
        // Free watchers lists for this variable, if possible:
        //if(watches[mkLit(v)].size() == 0) watches[mkLit(v)].clear(true);
        //if(watches[~mkLit(v)].size() == 0) watches[~mkLit(v)].clear(true);

        return self.backward_subsumption_check(formula, trail, watches);
    }

    // v is the index of the literal which we are trying to eliminate
    // Returns FALSE if clause is always satisfied.
    fn merge(&mut self, _ps: &Clause, _qs: &Clause, v: usize, size: &mut usize) -> bool {
        self.merges += 1;

        let ps_smallest = _ps.len() < _qs.len();
        let (ps, qs) = if ps_smallest { (_qs, _ps) } else { (_ps, _qs) };

        *size = ps.len() - 1;

        'outer: for q in qs.get_literals() {
            if q.index() != v {
                for p in ps.get_literals() {
                    if p.index() != q.index() {
                        if *p == !*q {
                            return false;
                        } else {
                            continue 'outer;
                        }
                    }
                }
                *size += 1;
            }
        }

        return true;
    }

    // v is the index of the literal which we are trying to eliminate
    // Returns FALSE if clause is always satisfied.
    fn merge_and_get(&mut self, _ps: &Clause, _qs: &Clause, v: usize, out_clause: &mut Vec<Lit>) -> bool {
        self.merges += 1;

        let (ps, qs) = if _ps.len() < _qs.len() { (_qs, _ps) } else { (_ps, _qs) };

        'outer: for q in qs.get_literals() {
            if q.index() != v {
                for p in ps.get_literals() {
                    if p.index() == q.index() {
                        if *p == !*q {
                            return false;
                        } else {
                            continue 'outer;
                        }
                    }
                }
                out_clause.push(*q);
            }
        }

        for p in ps.get_literals() {
            if p.index() != v {
                out_clause.push(*p);
            }
        }

        return true;
    }

    fn remove_clauses(&mut self, formula: &mut ClauseArena, v: usize) {
        debug!("Removing {}", v);
        // Mark all the clauses as deleted.
        formula.mark_clauses_as_deleted(&mut self.occurs[v]);

        // Remove the other places where the clauses are referenced.
        while let Some(cref) = self.occurs[v].pop() {
            for l in formula[cref].get_literals() {
                self.n_occ[l.to_watchidx()] -= 1;
                if let Some(index) = self.occurs[l.index()].iter().position(|value| *value == cref) {
                    debug!("Found {}", l);
                    self.occurs[l.index()].swap_remove(index);
                } else {
                    debug!("Not found {}", l);
                    //panic!();
                }
            }
        }
    }
}
*/
