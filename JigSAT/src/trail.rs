use crate::{
    assignments::*, clause_database::*, decision::*, lit::*, solver::*, solver_types::*, target_phase::*, watches::*,
};

use log::debug;

/*
#[derive(Debug)]
pub enum Reason {
    //Undefined,
    Decision,
    Unit,
    Long(usize),
}
*/

//const DECISION: usize = usize::MAX;
const UNIT: usize = usize::MAX;

pub const UNSET_LEVEL: u32 = u32::MAX;
pub const UNSET_REASON: usize = usize::MAX;

pub(crate) struct Trail {
    pub assignments: Assignments,
    pub lit_to_level: Vec<u32>,    // u32::MAX if unassigned
    pub lit_to_reason: Vec<usize>, // usize::MAX if unassigned
    pub trail: Vec<Lit>,
    pub curr_i: usize,
    pub decisions: Vec<usize>,
}

impl Trail {
    #[inline]
    pub(crate) fn decision_level(&self) -> u32 {
        self.decisions.len() as u32
    }

    pub(crate) fn new(f: &ClauseArena, a: Assignments) -> Trail {
        Trail {
            assignments: a,
            lit_to_level: vec![UNSET_LEVEL; f.num_vars()],
            lit_to_reason: vec![UNSET_REASON; f.num_vars()],
            trail: Vec::new(),
            curr_i: 0,
            decisions: Vec::new(),
        }
    }

    fn backstep(&mut self, formula: &ClauseArena, target_phase: &mut TargetPhase) -> usize {
        match self.trail.pop() {
            Some(lit) => {
                target_phase.set_polarity(lit.index(), lit.is_positive());

                self.assignments[lit.index()] = 2;
                self.lit_to_reason[lit.index()] = UNSET_REASON;
                //self.lit_to_level[step.lit.index()] = UNSET_LEVEL;

                lit.index()
            }
            None => {
                unreachable!();
            }
        }
    }

    pub(crate) fn restart(
        &mut self, formula: &mut ClauseArena, decisions: &mut impl Decisions, watches: &mut Watches, solver: &Solver,
        target_phase: &mut TargetPhase,
    ) {
        self.backtrack_safe(0, formula, decisions, target_phase);
        formula.collect_garbage_on_empty_trail(watches, solver);
    }

    pub(crate) fn backtrack_safe(
        &mut self, level: u32, formula: &ClauseArena, decisions: &mut impl Decisions, target_phase: &mut TargetPhase,
    ) {
        if level < self.decision_level() {
            self.backtrack_to(level, formula, decisions, target_phase);
        }
    }

    pub(crate) fn backtrack_to(
        &mut self, level: u32, formula: &ClauseArena, decisions: &mut impl Decisions, target_phase: &mut TargetPhase,
    ) {
        let how_many = self.trail.len() - self.decisions[level as usize];
        let mut i: usize = 0;

        //let mut curr = d.search; //VMTF
        //let mut timestamp = unsafe { d.linked_list.get_unchecked(curr).ts }; //VMTF

        while i < how_many {
            let idx = self.backstep(formula, target_phase);
            decisions.insert(idx);

            /*
            // VMTF
            let curr_timestamp = unsafe { d.linked_list.get_unchecked(idx).ts };
            if curr_timestamp > timestamp {
                timestamp = curr_timestamp;
                curr = idx;
            }
            */
            i += 1;
        }
        //d.search = curr; //VMTF

        while self.decision_level() > level {
            self.decisions.pop();
        }
        self.curr_i = self.trail.len();
    }

    pub(crate) fn enq_assignment(&mut self, lit: Lit, _f: &ClauseArena, reason: Cref) {
        // This should be refactored to not have to be a match (ie splitting up enq_assignment)
        assert!(lit.index() < _f.num_vars());
        self.lit_to_reason[lit.index()] = reason;

        self.lit_to_level[lit.index()] = self.decision_level();
        self.assignments.set_assignment(lit, _f, &self.trail);
        self.trail.push(lit);
    }

    pub(crate) fn enq_decision(
        &mut self, idx: usize, _f: &ClauseArena, target_phase: &TargetPhase, mode_is_focus: bool,
    ) {
        let trail_len = self.trail.len();
        self.decisions.push(trail_len);

        let dlevel = self.decision_level();
        self.lit_to_level[idx] = dlevel;

        let polarity = target_phase.choose_polarity(idx, mode_is_focus);
        self.assignments[idx] = polarity as u8;
        let lit = Lit::new(idx, polarity);

        assert!(lit.index() < _f.num_vars());
        self.trail.push(lit);
    }

    #[inline]
    pub(crate) fn learn_unit(
        &mut self, lit: Lit, formula: &mut ClauseArena, decisions: &mut impl Decisions, watches: &mut Watches,
        solver: &Solver, target_phase: &mut TargetPhase,
    ) {
        self.restart(formula, decisions, watches, solver, target_phase);
        assert!(lit.index() < formula.num_vars());
        self.enq_assignment(lit, formula, UNIT);
    }

    pub(crate) fn learn_units(&mut self, formula: &mut ClauseArena) -> Option<usize> {
        return None;
        //unimplemented!()
        /*
        let mut i = 0;
        while i < formula.len() {
            let clause = &formula[i];
            if clause.len() == 1 {
                let lit = clause[0];
                // This check should be removed by an invariant that the formula only contains unique clauses
                if lit.lit_set(&self.assignments) {
                    if lit.lit_unsat(&self.assignments) {
                        return Some(i);
                    }
                }
                self.enq_assignment(lit, formula, UNIT);
                formula.remove_clause_in_preprocessing(i);
            } else {
                i += 1;
            }
        }
        None
        */
    }
}

impl Trail {
    #[inline]
    pub(crate) fn learn_unit_in_preprocessing(&mut self, lit: Lit, formula: &ClauseArena) {
        debug!("Learned unit: {} in preproc", lit);
        self.enq_assignment(lit, formula, UNIT);
    }
}
