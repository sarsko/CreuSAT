use crate::{assignments::*, decision::*, formula::*, lit::*, solver::*, solver_types::*, target_phase::*, watches::*, clause_manager::{clause_manager::ClauseManager, common::CRef, self}};

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
const UNIT: CRef = CRef::MAX;

pub const UNSET_LEVEL: CRef = CRef::MAX;
pub const UNSET_REASON: CRef = CRef::MAX;

pub(crate) struct Trail {
    pub assignments: Assignments,
    pub lit_to_level: Vec<u32>,    // u32::MAX if unassigned
    pub lit_to_reason: Vec<CRef>, // u32::MAX if unassigned
    pub trail: Vec<Lit>,
    pub curr_i: usize,
    pub decisions: Vec<usize>,
}

impl Trail {
    #[inline]
    pub(crate) fn decision_level(&self) -> u32 {
        self.decisions.len() as u32
    }

    // TODO: Get num_vars from a.len() // 2 ?
    pub(crate) fn new(num_vars: usize, a: Assignments) -> Trail {
        Trail {
            assignments: a,
            lit_to_level: vec![UNSET_LEVEL; num_vars],
            lit_to_reason: vec![UNSET_REASON; num_vars],
            trail: Vec::new(),
            curr_i: 0,
            decisions: Vec::new(),
        }
    }

    fn backstep(&mut self, target_phase: &mut TargetPhase) -> usize {
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
        &mut self, clause_manager: &mut ClauseManager, decisions: &mut impl Decisions, watches: &mut Watches, solver: &Solver,
        target_phase: &mut TargetPhase,
    ) {
        self.backtrack_safe(0, decisions, target_phase);
        clause_manager.collect_garbage_on_empty_trail(watches, solver);
    }

    pub(crate) fn backtrack_safe(
        &mut self, level: u32, decisions: &mut impl Decisions, target_phase: &mut TargetPhase,
    ) {
        if level < self.decision_level() {
            self.backtrack_to(level, decisions, target_phase);
        }
    }

    pub(crate) fn backtrack_to(&mut self, level: u32, decisions: &mut impl Decisions, target_phase: &mut TargetPhase) {
        let how_many = self.trail.len() - self.decisions[level as usize];
        let mut i: usize = 0;

        //let mut curr = d.search; //VMTF
        //let mut timestamp = unsafe { d.linked_list.get_unchecked(curr).ts }; //VMTF

        while i < how_many {
            let idx = self.backstep(target_phase);
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

    pub(crate) fn enq_assignment(&mut self, lit: Lit, reason: CRef) {
        // This should be refactored to not have to be a match (ie splitting up enq_assignment)
        self.lit_to_reason[lit.index()] = reason;

        self.lit_to_level[lit.index()] = self.decision_level();
        self.assignments.set_assignment(lit);
        self.trail.push(lit);
    }

    pub(crate) fn enq_decision(&mut self, idx: usize, target_phase: &TargetPhase, mode_is_focus: bool) {
        let trail_len = self.trail.len();
        self.decisions.push(trail_len);

        let dlevel = self.decision_level();
        self.lit_to_level[idx] = dlevel;

        let polarity = target_phase.choose_polarity(idx, mode_is_focus);
        self.assignments[idx] = polarity as u8;
        let lit = Lit::new(idx, polarity);

        self.trail.push(lit);
    }

    #[inline]
    pub(crate) fn learn_unit(
        &mut self, lit: Lit, clause_manager: &mut ClauseManager, decisions: &mut impl Decisions, watches: &mut Watches,
        solver: &Solver, target_phase: &mut TargetPhase,
    ) {
        self.restart(clause_manager, decisions, watches, solver, target_phase);
        self.enq_assignment(lit, UNIT);
    }

    /*
    // TODO: I am not sure the algorithm is correct without this
    pub(crate) fn learn_units(&mut self, clause_manager: &mut ClauseManager) -> Option<usize> {
        let mut i = 0;
        while i < formula.len() {
            let clause = &formula[i];
            if clause.len() == 1 {
                let lit = clause[0];
                // This check should be removed by an invariant that the formula only contains unique clauses
                if lit.lit_unsat(&self.assignments) {
                    return Some(i);
                }
                self.enq_assignment(lit, formula, UNIT);
                formula.remove_clause_in_preprocessing(i);
            } else {
                i += 1;
            }
        }
        None
    }
    */
}

impl Trail {
    #[inline]
    pub(crate) fn learn_unit_in_preprocessing(&mut self, lit: Lit, formula: &Formula) {
        debug!("Learned unit: {} in preproc", lit);
        self.enq_assignment(lit, UNIT);
    }
}
