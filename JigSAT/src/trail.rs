use crate::{assignments::*, decision::*, formula::*, lit::*, watches::*, solver::*};

use log::debug;

#[derive(Debug)]
pub enum Reason {
    //Undefined,
    Decision,
    Unit,
    Long(usize),
}

#[derive(Debug)]
pub struct Step {
    pub lit: Lit,
    pub decision_level: u32,
    pub reason: Reason,
}

pub const UNSET_LEVEL: u32 = u32::MAX;
pub const UNSET_REASON: usize = usize::MAX;

pub struct Trail {
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

    fn backstep(&mut self, f: &Formula) -> usize {
        let last = self.trail.pop();
        match last {
            Some(step) => {
                self.assignments[step.lit.index()] += 2;
                // Removing this would be hard to prove lol.
                //self.lit_to_level[step.lit.index()] = u32::MAX;
                self.lit_to_reason[step.lit.index()] = UNSET_REASON;
                step.lit.index()
            }
            None => {
                unreachable!();
            }
        }
    }

    pub(crate) fn restart(&mut self, f: &mut Formula, d: &mut impl Decisions, watches: &mut Watches, s: &Solver) {
        self.backtrack_safe(0, f, d);
        f.collect_garbage_on_empty_trail(watches, s);

    }

    pub(crate) fn backtrack_safe(&mut self, level: u32, f: &Formula, d: &mut impl Decisions) {
        if level < self.decision_level() {
            self.backtrack_to(level, f, d);
        }
    }

    pub(crate) fn backtrack_to(&mut self, level: u32, f: &Formula, d: &mut impl Decisions) {
        let how_many = self.trail.len() - self.decisions[level as usize];
        let mut i: usize = 0;
        //let mut curr = d.search; //VMTF
        //let mut timestamp = unsafe { d.linked_list.get_unchecked(curr).ts }; //VMTF
        while i < how_many {
            let idx = self.backstep(f);
            d.insert(idx);
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
        match step.reason {
            Reason::Long(cref) => {
                self.lit_to_reason[step.lit.index()] = cref;
            }
            _ => {}
        }
        self.lit_to_level[step.lit.index()] = self.decision_level();
        self.assignments.set_assignment(step.lit, _f, &self.trail);
        self.trail.push(step);
    }

    pub(crate) fn enq_decision(&mut self, idx: usize, _f: &Formula) {
        let trail_len = self.trail.len();
        self.decisions.push(trail_len);
        let dlevel = self.decision_level();
        self.lit_to_level[idx] = dlevel;
        self.assignments[idx] -= 2;
        let lit = Lit::phase_saved(idx, &self.assignments);
        let step = Step { lit, decision_level: dlevel, reason: Reason::Decision };
        self.trail.push(step);
    }

    #[inline]
    pub(crate) fn learn_unit(&mut self, lit: Lit, formula: &mut Formula, d: &mut impl Decisions, watches: &mut Watches, s: &Solver) {
        self.restart(formula, d, watches, s);
        self.enq_assignment(Step { lit, decision_level: 0, reason: Reason::Unit }, formula);
    }

    pub(crate) fn learn_units(&mut self, f: &mut Formula) -> Option<usize> {
        let mut i = 0;
        while i < f.len() {
            let clause = &f[i];
            if clause.len() == 1 {
                let lit = clause[0];
                // This check should be removed by an invariant that the formula only contains unique clauses
                if lit.lit_set(&self.assignments) {
                    if lit.lit_unsat(&self.assignments) {
                        return Some(i);
                    }
                }
                self.enq_assignment(Step { lit, decision_level: 0, reason: Reason::Unit }, f);
                f.remove_clause_in_preprocessing(i);
            } else {
                i += 1;
            }
        }
        None
    }

    // Does a lesser check than Glucose
    pub(crate) fn locked(&self, lit: Lit) -> bool {
        lit.lit_sat(&self.assignments) && self.lit_to_reason[lit.index()] != UNSET_REASON
    }
}

impl Trail {
    #[inline]
    pub(crate) fn learn_unit_in_preprocessing(&mut self, lit: Lit, f: &Formula) {
        debug!("Learned unit: {} in preproc", lit);
        self.enq_assignment(Step { lit, decision_level: 0, reason: Reason::Unit }, f);
    }
}
