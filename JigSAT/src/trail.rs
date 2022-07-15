use crate::{assignments::*, decision::*, formula::*, lit::*, solver::*, solver_types::*, target_phase::*, watches::*};

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

//const Decision

const DECISION: usize = usize::MAX;
const UNIT: usize = usize::MAX;

#[derive(Debug)]
pub(crate) struct Step {
    pub lit: Lit,
    //decision_level: u32, // Turns out we never read this
    pub reason: Cref,
}

pub const UNSET_LEVEL: u32 = u32::MAX;
pub const UNSET_REASON: usize = usize::MAX;

pub(crate) struct Trail {
    pub assignments: Assignments,
    pub lit_to_level: Vec<u32>,    // u32::MAX if unassigned
    pub lit_to_reason: Vec<usize>, // usize::MAX if unassigned
    pub trail: Vec<Step>,
    pub curr_i: usize,
    pub decisions: Vec<usize>,
}

impl Trail {
    #[inline]
    pub(crate) fn decision_level(&self) -> u32 {
        self.decisions.len() as u32
    }

    pub(crate) fn new(f: &Formula, a: Assignments) -> Trail {
        Trail {
            assignments: a,
            lit_to_level: vec![UNSET_LEVEL; f.num_vars],
            lit_to_reason: vec![UNSET_REASON; f.num_vars],
            trail: Vec::new(),
            curr_i: 0,
            decisions: Vec::new(),
        }
    }

    fn backstep(&mut self, formula: &Formula, target_phase: &mut TargetPhase) -> usize {
        match self.trail.pop() {
            Some(step) => {
                target_phase.set_polarity(step.lit.index(), step.lit.is_positive());

                self.assignments[step.lit.index()] = 2;
                self.lit_to_reason[step.lit.index()] = UNSET_REASON;
                //self.lit_to_level[step.lit.index()] = UNSET_LEVEL;

                step.lit.index()
            }
            None => {
                unreachable!();
            }
        }
    }

    pub(crate) fn restart(
        &mut self, formula: &mut Formula, decisions: &mut impl Decisions, watches: &mut Watches, solver: &Solver,
        target_phase: &mut TargetPhase,
    ) {
        self.backtrack_safe(0, formula, decisions, target_phase);
        formula.collect_garbage_on_empty_trail(watches, solver);
    }

    pub(crate) fn backtrack_safe(
        &mut self, level: u32, formula: &Formula, decisions: &mut impl Decisions, target_phase: &mut TargetPhase,
    ) {
        if level < self.decision_level() {
            self.backtrack_to(level, formula, decisions, target_phase);
        }
    }

    pub(crate) fn backtrack_to(
        &mut self, level: u32, formula: &Formula, decisions: &mut impl Decisions, target_phase: &mut TargetPhase,
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

    pub(crate) fn enq_assignment(&mut self, step: Step, _f: &Formula) {
        // This should be refactored to not have to be a match (ie splitting up enq_assignment)
        if step.reason < usize::MAX - 1 {
            self.lit_to_reason[step.lit.index()] = step.reason;
        }

        self.lit_to_level[step.lit.index()] = self.decision_level();
        self.assignments.set_assignment(step.lit, _f, &self.trail);
        self.trail.push(step);
    }

    pub(crate) fn enq_decision(&mut self, idx: usize, _f: &Formula, target_phase: &TargetPhase, mode_is_focus: bool) {
        let trail_len = self.trail.len();
        self.decisions.push(trail_len);

        let dlevel = self.decision_level();
        self.lit_to_level[idx] = dlevel;

        let polarity = target_phase.choose_polarity(idx, mode_is_focus);
        self.assignments[idx] = polarity as u8;
        let lit = Lit::new(idx, polarity);

        let step = Step { lit /*, decision_level: dlevel*/, reason: DECISION };
        self.trail.push(step);
    }

    #[inline]
    pub(crate) fn learn_unit(
        &mut self, lit: Lit, formula: &mut Formula, decisions: &mut impl Decisions, watches: &mut Watches,
        solver: &Solver, target_phase: &mut TargetPhase,
    ) {
        self.restart(formula, decisions, watches, solver, target_phase);
        self.enq_assignment(Step { lit /*, decision_level: 0*/, reason: UNIT }, formula);
    }

    pub(crate) fn learn_units(&mut self, formula: &mut Formula) -> Option<usize> {
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
                self.enq_assignment(Step { lit /*, decision_level: 0*/, reason: UNIT }, formula);
                formula.remove_clause_in_preprocessing(i);
            } else {
                i += 1;
            }
        }
        None
    }

    // Does a more restrictive check than Glucose
    // TODO: Add the last part of the check.
    pub(crate) fn locked(&self, lit: Lit) -> bool {
        lit.lit_sat(&self.assignments) && self.lit_to_reason[lit.index()] != UNSET_REASON
    }
}

impl Trail {
    #[inline]
    pub(crate) fn learn_unit_in_preprocessing(&mut self, lit: Lit, f: &Formula) {
        debug!("Learned unit: {} in preproc", lit);
        self.enq_assignment(Step { lit /*, decision_level: 0*/, reason: UNIT }, f);
    }
}
