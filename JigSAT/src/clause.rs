use crate::{formula::*, lit::*, solver::Solver, trail::*};
use std::{ops::{Index}, cmp::Ordering};

pub struct Clause {
    pub deleted: bool,
    pub lbd: u32,
    lits: Vec<Lit>,
}


impl Index<usize> for Clause {
    type Output = Lit;
    #[inline]
    fn index(&self, i: usize) -> &Lit {
        //#[cfg(feature = "unsafe_access")]
        unsafe {
            self.lits.get_unchecked(i)
        }
        //#[cfg(not(feature = "unsafe_access"))]
        //&self.lits[i]
    }
}

impl Clause {
    pub fn swap(&mut self, i: usize, j: usize) {
        self.lits.swap(i, j);
    }

    pub fn pop(&mut self) {
        self.lits.pop();
    }

    pub fn less_than(&self, other: &Clause) -> Ordering {
        if self.len() == 2 {
            if other.len() == 2 {
                Ordering::Equal
            } else {
                Ordering::Less
            }
        } else if other.len() == 2 {
            Ordering::Greater
        } else if self.lbd < other.lbd {
            Ordering::Less
        } else if self.lbd > other.lbd {
            Ordering::Greater
        } else if self.len() < other.len() {
            Ordering::Less
        } else if self.len() > other.len() {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }

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
        false
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
        true
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.lits.len()
    }

    pub fn clause_from_vec(vec: &[Lit]) -> Clause {
        Clause { deleted: false, lbd: 0, lits: vec.to_vec() }
    }

    #[inline(always)]
    fn move_to_end(&mut self, idx: usize, _f: &Formula) {
        let end = self.len() - 1;
        self.swap(idx, end);
    }

    #[inline(always)]
    pub fn remove_from_clause(&mut self, idx: usize, _f: &Formula) {
        self.move_to_end(idx, _f);
        self.pop();
    }

    fn calc_lbd(lits: &Vec<Lit>, trail: &Trail, solver: &mut Solver) -> u32 {
        // We don't bother calculating for long clauses.
        if lits.len() >= 2024 {
            return 2024;
        }
        let mut lbd: u32 = 0;
        let mut i = 0;
        while i < lits.len() {
            let level = trail.lit_to_level[lits[i].index()];
            if solver.perm_diff[level as usize] != solver.num_conflicts {
                solver.perm_diff[level as usize] = solver.num_conflicts;
                lbd += 1;
            }
            i += 1;
        }
        lbd
    }

    pub fn new_and_set_lbd(lits: Vec<Lit>, trail: &Trail, solver: &mut Solver) -> Clause {
        let lbd = Clause::calc_lbd(&lits, trail, solver);
        Clause { deleted: false, lbd, lits }
    }

}
