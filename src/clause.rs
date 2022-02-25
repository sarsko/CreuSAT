use crate::lit::*;
use crate::assignments::*;
use crate::formula::*;

pub struct Clause(pub Vec<Lit>);

impl Clause {
    pub fn check_if_unit(&self, a: &Assignments, f: &Formula) -> bool {
        let mut i: usize = 0;
        let mut unassigned: usize = 0;
        let mut k: usize = 0;
        while i < self.0.len() {
            let lit = self.0[i];
            let res = &a.0[lit.idx];
            match res {
                AssignedState::Positive => {
                    if lit.polarity {
                        return false;
                    }
                },
                AssignedState::Negative => {
                    if !lit.polarity {
                        return false;
                    }
                },
                AssignedState::Unset => {
                    if unassigned >= 1 {
                        return false;
                    }
                    k = i;
                    unassigned += 1;
                },
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
        while i < self.0.len() {
            let lit = self.0[i];
            let res = &a.0[lit.idx];
            match res {
                AssignedState::Positive => {},
                AssignedState::Negative => {},
                AssignedState::Unset => { return lit; },
            }
            i += 1;
        }
        panic!();
    }
}