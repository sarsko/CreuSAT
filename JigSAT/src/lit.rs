use ::std::ops;

use crate::{assignments::*};

#[derive(Clone, Copy, Eq, PartialEq)]
pub struct Lit {
    code: u32
}

impl Lit {
    pub fn index(self) -> usize {
        (self.code >> 1) as usize
    }

    pub fn is_positive(self) -> bool {
        self.code & 1 != 0
    }

    pub fn check_lit_invariant(self, n: usize) -> bool {
        return self.index() < n;
    }

    pub fn lit_sat(self, a: &Assignments) -> bool {
        a.0[self.index()] == self.is_positive() as u8
    }

    pub fn lit_unsat(self, a: &Assignments) -> bool {
        a.0[self.index()] == !self.is_positive() as u8
    }

    pub fn lit_unset(self, a: &Assignments) -> bool {
        a.0[self.index()] >= 2
    }

    pub fn lit_set(self, a: &Assignments) -> bool {
        a.0[self.index()] < 2
    }

    pub fn to_watchidx(self) -> usize {
        self.code as usize
    }
    pub fn to_neg_watchidx(self) -> usize {
        (!self).code as usize
    }

    pub fn phase_saved(idx: usize, assignments: &Assignments) -> Lit {
        Lit {
            code: (idx << 1) as u32 | ((assignments.0[idx] == 1) as u32)
        }
    }

    // This is only called in the parser
    pub fn new(idx: usize, polarity: bool) -> Lit {
        Lit {
            code: (idx << 1) as u32 | (polarity as u32)
        }
    }
}

impl ops::Not for Lit {
    type Output = Lit;

    #[inline]
    fn not(self) -> Lit {
        Lit { code: self.code ^ 1 }
    }
}
