use crate::lit::*;
use crate::assignments::*;
use crate::formula::*;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Clause {
    pub first: Lit,
    pub second: Lit,
    pub rest: Vec<Lit>
}

impl Clause {
    #[inline]
    pub fn clause_from_vec(vec: &Vec<Lit>) -> Clause {
        Clause {
            first: vec[0],
            second: vec[1],
            rest: vec[2..].to_vec()
        }
    }
    pub fn check_if_unit(&self, a: &Assignments, f: &Formula) -> bool {
        let mut i: usize = 0;
        let mut unassigned: usize = 0;
        let res = a.0[self.first.idx];
        if self.first.polarity as u8 == res {
            return false;
        } else if res >= 2 {
            unassigned += 1;
        }
        let res = a.0[self.second.idx];
        if self.second.polarity as u8 == res {
            return false;
        } else if res >= 2 {
            unassigned += 1;
        }
        while i < self.rest.len() {
            let lit = self.rest[i];
            let res = a.0[lit.idx];
            if lit.polarity as u8 == res {
                return false;
            } else if res >= 2 {
                unassigned += 1;
            }
            i += 1;
        }
        if unassigned == 1 {
            true
        } else {
            false
        }
    }

    pub fn get_unit(&self, a: &Assignments, f: &Formula) -> Lit {
        let mut i: usize = 0;
        let res = a.0[self.first.idx];
        if res >= 2 {
            return self.first;
        }         
        let res = a.0[self.second.idx];
        if res >= 2 {
            return self.second;
        } 
        while i < self.rest.len() {
            let lit = self.rest[i];
            let res = a.0[lit.idx];
            if res >= 2 {
                return lit;
            }
            i += 1;
        }
        panic!();
    }
}