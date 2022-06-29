use crate::{assignments::*, decision::*, formula::*, lit::*};

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
    pub fn decision_level(&self) -> u32 {
        self.decisions.len() as u32
    }

    pub fn new(f: &Formula, a: Assignments) -> Trail {
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

    pub fn backtrack_safe(&mut self, level: u32, f: &Formula, d: &mut Decisions) {
        if level < self.decision_level() {
            self.backtrack_to(level, f, d);
        }
    }

    pub fn backtrack_to(&mut self, level: u32, f: &Formula, d: &mut Decisions) {
        let how_many = self.trail.len() - self.decisions[level as usize];
        let mut i: usize = 0;
        let mut curr = d.search;
        let mut timestamp = unsafe { d.linked_list.get_unchecked(curr).ts };
        while i < how_many {
            let idx = self.backstep(f);
            let curr_timestamp = unsafe { d.linked_list.get_unchecked(idx).ts };
            if curr_timestamp > timestamp {
                timestamp = curr_timestamp;
                curr = idx;
            }
            i += 1;
        }
        d.search = curr;

        while self.decision_level() > level {
            self.decisions.pop();
        }
        self.curr_i = self.trail.len();
    }

    pub fn enq_assignment(&mut self, step: Step, _f: &Formula) {
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

    pub fn enq_decision(&mut self, idx: usize, _f: &Formula) {
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
    pub fn learn_unit(&mut self, lit: Lit, f: &Formula, d: &mut Decisions) {
        self.backtrack_safe(0, f, d);
        self.enq_assignment(Step { lit, decision_level: 0, reason: Reason::Unit }, f);
    }

    pub fn learn_units(&mut self, f: &mut Formula) -> Option<usize> {
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
}
