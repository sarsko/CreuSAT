extern crate creusot_contracts;

use creusot_contracts::logic::Ghost;
use creusot_contracts::std::*;
use creusot_contracts::*;

//use crate::creusot_contracts::std::iter::IteratorSpec;

//#[allow(unused_features)]
#[cfg(feature = "contracts")]
use crate::logic::logic::*;

#[cfg(feature = "contracts")]
impl creusot_contracts::Model for Clause {
    type ModelTy = ClauseLogic;

    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        pearlite! { ClauseLogic { lits: absurd } }
    }
}

#[cfg(feature = "contracts")]
impl creusot_contracts::Model for ClauseDB {
    type ModelTy = FormulaLogic;

    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        pearlite! { FormulaLogic ( absurd ) }
    }
}

#[cfg(feature = "contracts")]
impl creusot_contracts::Model for Lit {
    type ModelTy = LitLogic;

    #[logic]
    fn model(self) -> Self::ModelTy {
        pearlite! { LitLogic { idx: @self.idx, polarity: self.polarity } }
    }
}

pub enum SatResult {
    Sat,
    Unsat,
    Unknown,
}

enum UnsatOrContinue {
    Unsat,
    Continue,
}

pub(crate) enum LitEvalRes {
    Sat,
    Unsat,
    Unset,
}

pub(crate) enum ClauseEvalRes {
    Unit,
    Unsat,
    Other,
}

#[derive(Copy, Clone)]
pub struct Lit {
    idx: usize,
    polarity: bool,
}

impl Lit {
    #[requires((@self).idx_less_than((@trail.assignments).len()))]
    pub(crate) fn eval(&self, trail: &Trail) -> LitEvalRes {
        let assn = trail.assignments[self.idx];
        if assn >= 2 {
            return LitEvalRes::Unset;
        }
        if assn == 1 && self.polarity || assn == 0 && !self.polarity {
            return LitEvalRes::Sat;
        }
        LitEvalRes::Unsat
    }

    pub(crate) fn index(self) -> usize {
        self.idx
    }

    pub(crate) fn new(idx: usize, polarity: bool) -> Self {
        Lit { idx, polarity }
    }

    pub(crate) fn from_dimacs(n: i32) -> Self {
        assert!(n != 0);
        Lit { idx: n.abs() as usize - 1, polarity: n > 0 }
    }
}

use ::std::ops;
impl ops::Not for Lit {
    type Output = Lit;

    #[inline]
    fn not(self) -> Lit {
        Lit { idx: self.idx, polarity: !self.polarity }
    }
}

#[derive(Clone)]
pub struct Clause {
    lits: Vec<Lit>,
}

impl Clause {
    pub(crate) fn new(lits: Vec<Lit>) -> Self {
        Clause { lits }
    }

    #[requires((@self).idxes_less_than((@trail.assignments).len()))]
    #[ensures(match result {
        ClauseEvalRes::Other => true,
        ClauseEvalRes::Unsat => true,
        ClauseEvalRes::Unit  => true,//(@(^self).lits)[0].sat(@trail.assignments) && // rest unsat,
    })]
    pub(crate) fn is_unit_or_unsat(&mut self, trail: &Trail) -> ClauseEvalRes {
        let mut potential_unit_idx: Option<usize> = None;
        let mut i: usize = 0;
        #[invariant(pot_unit_in_range, match potential_unit_lit {
            None => true,
            Some(lit) => (@lit).idx_less_than((@trail.assignments).len()),
        })]
        //for lit in &self.lits {
        while i < self.lits.len() {
            let lit = self.lits[i];
            proof_assert!((@lit).idx_less_than((@trail.assignments).len()));
            match lit.eval(trail) {
                LitEvalRes::Sat => return ClauseEvalRes::Other,
                LitEvalRes::Unsat => {}
                LitEvalRes::Unset => match potential_unit_idx {
                    Some(_) => return ClauseEvalRes::Other,
                    None => potential_unit_idx = Some(i),
                },
            }
            i += 1;
        }
        match potential_unit_idx {
            Some(i) => {
                self.lits.swap(i, 0);
                ClauseEvalRes::Unit
            }
            None => ClauseEvalRes::Unsat,
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.lits.len()
    }
}

pub struct ClauseDB {
    clauses: Vec<Clause>,
    pub(crate) num_vars: usize,
}

impl ClauseDB {
    pub(crate) fn new() -> Self {
        ClauseDB { clauses: Vec::new(), num_vars: 0 }
    }

    pub(crate) fn add_unwatched_clause(&mut self, clause: Clause) {
        for e in &clause.lits {
            if e.index() >= self.num_vars {
                self.num_vars = e.index() + 1;
            }
        }
        self.clauses.push(clause);
    }
}

pub struct Trail {
    assignments: Assignments,
    trail: Vec<Lit>,
    lit_to_reason: Vec<Cref>,
    lit_to_level: Vec<usize>,
    decisions: Vec<usize>,
}

impl Trail {
    pub(crate) fn new(num_vars: usize) -> Self {
        Trail {
            assignments: vec![2u8; num_vars],
            trail: Vec::new(),
            lit_to_reason: vec![usize::MAX; num_vars], // TODO: Swap to UNSET_REASON when consts become supported
            lit_to_level: vec![usize::MAX; num_vars],  // TODO: Swap to UNSET_LEVEL when consts become supported
            decisions: Vec::new(),
        }
    }

    #[inline(always)]
    #[ensures(@result == (@self.decisions).len())]
    pub(crate) fn decision_level(&self) -> usize {
        self.decisions.len()
    }

    pub(crate) fn restart(&mut self) {
        if self.decision_level() > 0 {
            let how_many = self.trail.len() - self.decisions[0];
            let mut i: usize = 0;

            while i < how_many {
                let lit = self.trail.pop().unwrap();

                self.assignments[lit.index()] = 2;
                self.lit_to_reason[lit.index()] = usize::MAX;

                i += 1;
            }

            while self.decision_level() > 0 {
                self.decisions.pop();
            }
        }
    }
}

pub(crate) type AssignedState = u8;
pub(crate) type Cref = usize;

// Creusot doesn't support consts :((((((
//pub(crate) const UNSET_REASON: Cref = usize::MAX;
//pub(crate) const UNSET_LEVEL: Cref = usize::MAX;

pub(crate) type Assignments = Vec<AssignedState>;

//use ::std::ops::{Index, IndexMut};

pub(crate) struct Decisions {}

impl Decisions {
    #[ensures(match result {
        Some(idx) => @idx < (@assignments).len() && unset((@assignments)[@idx]),
        None      => forall<i: _> 0 <= i && i < (@assignments).len() ==> !unset((@assignments)[i]),
    })]
    pub(crate) fn make_decision(assignments: &Assignments) -> Option<usize> {
        let mut i = 0;
        #[invariant(less_unassigned, forall<j: _> 0 <= j && j < @i ==> !unset((@assignments)[j]))]
        while i < assignments.len() {
            // TODO: Abstraction barrier
            if assignments[i] >= 2 {
                return Some(i);
            }
            i += 1;
        }
        None
    }
}

//#[requires(@lit.idx < (@trail.assignments).len())]
#[requires((@lit).idx_less_than((@trail.assignments).len()))]
fn propagate_literal(idx: usize, clause_db: &ClauseDB, trail: &mut Trail) {
    let lit = clause_db.clauses[idx].lits[0];

    match lit.polarity {
        true => trail.assignments[lit.idx] = 1,
        false => trail.assignments[lit.idx] = 0,
    }

    trail.trail.push(lit);
    trail.lit_to_level[lit.index()] = trail.decision_level();
    trail.lit_to_reason[lit.index()] = idx;
}

fn analyze_and_learn(cref: Cref, clause_db: &mut ClauseDB, trail: &mut Trail) -> UnsatOrContinue {
    let decisionlevel = trail.decision_level();
    if decisionlevel == 0 {
        return UnsatOrContinue::Unsat;
    }
    let mut seen = vec![false; clause_db.num_vars];
    let mut out_learnt: Vec<Lit> = vec![Lit::new(0, true); 1];
    let mut path_c = 0;
    let mut confl = cref;
    let mut i = trail.trail.len();

    loop {
        let clause = &clause_db.clauses[confl];
        let mut k = if confl == cref { 0 } else { 1 };
        while k < clause.len() {
            let lit = clause.lits[k];
            if !seen[lit.index()] {
                let level = trail.lit_to_level[lit.index()];

                if level > 0 {
                    seen[lit.index()] = true;

                    if level >= decisionlevel {
                        path_c += 1;
                    } else {
                        out_learnt.push(lit);
                    }
                }
            }
            k += 1;
        }
        let next = {
            loop {
                i -= 1;
                if seen[trail.trail[i].index()] {
                    break;
                }
            }
            &trail.trail[i]
        };
        seen[next.index()] = false;
        path_c -= 1;
        if path_c == 0 {
            out_learnt[0] = !*next;
            break;
        }
        confl = trail.lit_to_reason[next.index()];
    }

    if out_learnt.len() == 1 {
        trail.restart();

        let lit = out_learnt[0];

        trail.lit_to_level[lit.index()] = 0;

        match lit.polarity {
            true => trail.assignments[lit.index()] = 1,
            false => trail.assignments[lit.index()] = 0,
        }

        trail.trail.push(lit);
    } else {
        /*
        let mut max_i: usize = 1;
        let mut max_level = trail.lit_to_level[out_learnt[1].index()];
        i = 2;
        while i < out_learnt.len() {
            let level = trail.lit_to_level[out_learnt[i].index()];
            if level > max_level {
                max_level = level;
                max_i = i;
            }
            i += 1;
        }
        out_learnt.swap(1, max_i);
        */

        let mut clause = Clause::new(out_learnt);
        clause_db.clauses.push(clause);

        trail.restart(); // No backtracking to asserting level
    }
    UnsatOrContinue::Continue
}

#[ensures((@trail.assignments).len() == (@(^trail).assignments).len())]
#[requires((@clause_db).idxes_less_than((@trail.assignments).len()))]
#[ensures((@^clause_db).idxes_less_than((@trail.assignments).len()))]
fn unit_prop_loop(clause_db: &mut ClauseDB, trail: &mut Trail) -> UnsatOrContinue {
    let mut i: usize = 0;
    let old_trail: Ghost<&mut Trail> = ghost!(trail);

    #[invariant(i_less, @i <= (@clause_db.clauses).len())]
    #[invariant(trail_len_unchanged, (@old_trail.inner().assignments).len() == (@trail.assignments).len())]
    #[invariant(idxes_in_range, (@clause_db).idxes_less_than((@trail.assignments).len()))]
    while i < clause_db.clauses.len() {
        let clause = &mut clause_db.clauses[i];
        match clause.is_unit_or_unsat(trail) {
            ClauseEvalRes::Unit => {
                propagate_literal(i, clause_db, trail);
                i = 0
            }
            ClauseEvalRes::Unsat => match analyze_and_learn(i, clause_db, trail) {
                UnsatOrContinue::Unsat => return UnsatOrContinue::Unsat,
                UnsatOrContinue::Continue => i = 0,
            },
            ClauseEvalRes::Other => {
                i += 1;
            }
        }
    }

    UnsatOrContinue::Continue
}

//#[ensures(result == SatResult::Sat)]
pub fn solve(mut clause_db: ClauseDB) -> SatResult {
    let mut trail = Trail::new(clause_db.num_vars);

    //#[invariant(trail_len_unchanged, (@old_trail.inner().assignments).len() == (@trail.assignments).len())]

    // This leads to creusot panic
    //#[invariant(idxes_in_range, (@clause_db).idxes_less_than((@trail.assignments).len()))]
    loop {
        match unit_prop_loop(&mut clause_db, &mut trail) {
            UnsatOrContinue::Unsat => return SatResult::Unsat,
            UnsatOrContinue::Continue => {}
        }
        match Decisions::make_decision(&trail.assignments) {
            None => return SatResult::Sat,
            Some(idx) => {
                trail.decisions.push(trail.trail.len());
                trail.lit_to_level[idx] = trail.decision_level();

                trail.assignments[idx] = 0; // We always set false.
                trail.trail.push(Lit::new(idx, false));
            }
        }
    }
}
