use crate::assignments::*;
use crate::clause::*;
use crate::lit::*;
use crate::watches::*;

#[derive(Debug)]
pub struct Formula {
    pub clauses: Vec<Clause>,
    pub num_vars: usize,
}

impl Formula {
    /*
    #[allow(dead_code)]
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
    */

    pub fn add_clause(&mut self, clause: &Vec<Lit>, watches: &mut Watches) -> usize {
        let clause = Clause::clause_from_vec(clause);
        let cref = self.clauses.len();
        watches.add_watcher(clause.first, cref);
        watches.add_watcher(clause.second, cref);
        self.clauses.push(clause);
        cref
    }

    // Or people could just make correct cnfs
    pub fn remove_duplicates(&mut self) {
        use std::collections::HashSet;
        let mut uniques = HashSet::new();
        self.clauses.retain(|e| uniques.insert(e.clone()));
    }
}
