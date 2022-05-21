use crate::{assignments::*, formula::*, lit::*};

pub struct Clause {
    pub deleted: bool,
    pub rest: Vec<Lit>,
}


impl Clone for Clause {
    fn clone(&self) -> Self {
        Clause { deleted: self.deleted, rest: self.rest.clone() }
    }
}

//#[derive(Copy, Clone, Eq)]
pub enum ClauseState {
    Sat,
    Unsat,
    Unit,
    Unknown,
    Err(usize),
}

impl Clause {
    pub fn check_clause_invariant(&self, n: usize) -> bool {
        let mut i: usize = 0;
        while i < self.len() {
            if !self.rest[i].check_lit_invariant(n) {
                return false;
            }
            i += 1;
        }
        if self.no_duplicates() {
            return true;
        }
        return false;
    }

    pub fn no_duplicates(&self) -> bool {
        let mut i: usize = 0;
        while i < self.rest.len() {
            let lit1 = self.rest[i];
            let mut j: usize = 0;
            while j < i {
                let lit2 = self.rest[j];
                if lit1.index() == lit2.index() {
                    return false;
                }
                j += 1;
            }
            i += 1;
        }
        return true;
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.rest.len()
    }

    pub fn clause_from_vec(vec: &Vec<Lit>) -> Clause {
        Clause { deleted: false, rest: vec.clone() }
    }

    #[inline(always)]
    fn move_to_end(&mut self, idx: usize, _f: &Formula) {
        let end = self.rest.len() - 1;
        self.rest.swap(idx, end);
    }

    #[inline(always)]
    pub fn remove_from_clause(&mut self, idx: usize, _f: &Formula) {
        self.move_to_end(idx, _f);
        self.rest.pop();
    }

    // This is an ugly runtime check
    pub fn unit_and_unset(&self, a: &Assignments, _f: &Formula) -> bool {
        let mut i: usize = 1;
        while i < self.rest.len() {
            if !self.rest[i].lit_unsat(a) {
                return false;
            }
            i += 1;
        }
        return self.rest[0].lit_unset(a);
    }
}
