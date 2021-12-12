use crate::assignments::*;
use crate::clause::*;

pub struct Formula {
    pub clauses: Vec<Clause>,
    pub num_vars: usize,
}

impl Formula {
    pub fn contains_empty(&self, a: &Assignments) -> bool {
        let mut i = 0;
        while i < self.clauses.len() {
            let clause = &self.clauses[i];
            if clause.is_unsat(a) {
                return true;
            }
            i += 1
        }
        return false;
    }
}