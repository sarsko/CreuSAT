use crate::{assignments::*, decision::*, formula::*, lit::*};

#[derive(Debug)]
pub enum Reason {
    //Undefined,
    Decision,
    Unit,
    Long(usize),
}

pub struct Step {
    pub lit: Lit,
    pub decision_level: u32,
    pub reason: Reason,
}

pub struct Trail {
    pub assignments: Assignments,
    pub lit_to_level: Vec<u32>, // usize::MAX if unassigned
    pub trail: Vec<Step>,
    pub curr_i: usize,
    pub decisions: Vec<usize>,
}

impl Trail {
    pub fn decision_level(&self) -> u32 {
        self.decisions.len() as u32
    }

    pub fn new(f: &Formula, a: Assignments) -> Trail {
        Trail {
            assignments: a,
            lit_to_level: vec![u32::MAX; f.num_vars],
            trail: Vec::new(),
            curr_i: 0,
            decisions: Vec::new(),
        }
    }

    fn backstep(&mut self, f: &Formula) -> usize {
        let last = self.trail.pop();
        match last {
            Some(step) => {
                self.assignments.0[step.lit.index()] += 2; 
                self.lit_to_level[step.lit.index()] = u32::MAX;
                return step.lit.index();
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
        let mut timestamp = d.linked_list[curr].ts;
        while i < how_many {
            let idx = self.backstep(f);
            let curr_timestamp = d.linked_list[idx].ts;
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
        self.curr_i = level as usize;
    }

    pub fn enq_assignment(&mut self, step: Step, _f: &Formula) {
        self.lit_to_level[step.lit.index()] = self.decision_level();
        let trail = &self.trail;

        self.assignments.set_assignment(step.lit, _f, trail);

        self.trail.push(step);
    }

    pub fn enq_decision(&mut self, idx: usize, _f: &Formula) {
        let trail_len = self.trail.len();
        self.decisions.push(trail_len);
        let dlevel = self.decision_level();
        self.lit_to_level[idx] = dlevel;
        self.assignments.0[idx] -= 2;
        let lit = Lit::phase_saved(idx, &self.assignments);

        let step = Step { lit: lit, decision_level: dlevel, reason: Reason::Decision };

        self.trail.push(step);
    }

    pub fn learn_unit(&mut self, lit: Lit, f: &Formula, d: &mut Decisions) -> Result<(), ()> {
        if self.decision_level() > 0 {
            self.backtrack_to(0, f, d);
        }
        self.enq_assignment(Step { lit: lit, decision_level: 0, reason: Reason::Unit }, f);
        Ok(())
    }

    pub fn learn_units(&mut self, f: &Formula, d: &mut Decisions) -> Option<usize> {
        let mut i = 0;
        while i < f.clauses.len() {
            let clause = &f.clauses[i];
            if clause.rest.len() == 1 {
                let lit = clause.rest[0];
                // This check should be removed by an invariant that the formula only contains unique clauses
                if lit.lit_set(&self.assignments) {
                    if lit.lit_unsat(&self.assignments) {
                        return Some(i);
                    }
                } else {
                    self.learn_unit(lit, f, d);
                }
            }
            i += 1;
        }
        return None;
    }
}