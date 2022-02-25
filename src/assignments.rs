use crate::lit::*;
use crate::clause::*;
use crate::formula::*;

pub struct Assignments(pub Vec<u8>);


impl Assignments {
    pub fn clone(&self) -> Self {
        let mut out = Vec::new();
        let mut i: usize = 0;
        while i < self.0.len() {
            let curr = self.0[i];
            out.push(curr.clone());
            i += 1;
        }
        Assignments(out)
    }

    pub fn new(f: &Formula) -> Self {
        let mut assign: Vec<u8> = Vec::new();
        let mut i: usize = 0;
        while i < f.num_vars {
            assign.push(2);
            i += 1
        }
        Assignments(assign)
    }

    pub fn find_unassigned(&self) -> usize {
        let mut i: usize = 0;
        while i < self.0.len() {
            let curr = self.0[i];
            if curr >= 2 {
                return i;
            }
            i += 1;
        }
        unreachable!()
    }

    pub fn unit_prop_once(&mut self, i: usize, f: &Formula) -> bool {
        let clause = &f.clauses[i];
        if clause.check_if_unit(self, f) {
            let lit = clause.get_unit(self, f);
            if lit.polarity {
                self.0[lit.idx] = 1;
            } else {
                self.0[lit.idx] = 0;
            }
            return true;
        }
        return false;
    }

    pub fn unit_propagate(&mut self, f: &Formula) -> bool {
        let mut i: usize = 0;
        let mut out = false;
        while i < f.clauses.len() {
            if self.unit_prop_once(i, f) {
                out = true;
            }
            i += 1
        }
        return out;
    }

    pub fn do_unit_propagation(&mut self, f: &Formula) {
        while self.unit_propagate(f) {}
    }
}