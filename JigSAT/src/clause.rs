use crate::{formula::*, lit::*};
use std::{ops::{Index}};

pub struct Clause {
    pub deleted: bool,
    pub lbd: u32,
    pub rest: Vec<Lit>,
}


impl Clone for Clause {
    fn clone(&self) -> Self {
        Clause { deleted: self.deleted, lbd: self.lbd, rest: self.rest.clone() }
    }
}

impl Index<usize> for Clause {
    type Output = Lit;
    #[inline]
    fn index(&self, i: usize) -> &Lit {
        //#[cfg(feature = "unsafe_access")]
        unsafe {
            self.rest.get_unchecked(i)
        }
        //#[cfg(not(feature = "unsafe_access"))]
        //&self.lits[i]
    }
}

impl Clause {
    pub fn check_clause_invariant(&self, n: usize) -> bool {
        let mut i: usize = 0;
        while i < self.len() {
            if !self[i].check_lit_invariant(n) {
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
        while i < self.len() {
            let lit1 = self[i];
            let mut j: usize = 0;
            while j < i {
                let lit2 = self[j];
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
        Clause { deleted: false, lbd: 0, rest: vec.clone() }
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

}
