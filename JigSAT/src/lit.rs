use ::std::ops;

use crate::{assignments::*};

#[derive(Clone, Copy)]
pub struct Lit {
    pub idx: usize,
    pub polarity: bool,
}


impl Lit {
    pub fn index(self) -> usize {
        self.idx
    }

    pub fn is_positive(self) -> bool {
        self.polarity
    }

    pub fn check_lit_invariant(&self, n: usize) -> bool {
        return self.index() < n;
    }

    pub fn lit_sat(self, a: &Assignments) -> bool {
        match self.is_positive() {
            true => (a.0[self.index()] == 1),
            false => (a.0[self.index()] == 0),
        }
    }

    pub fn lit_unsat(self, a: &Assignments) -> bool {
        match self.is_positive() {
            true => (a.0[self.index()] == 0),
            false => (a.0[self.index()] == 1),
        }
    }

    pub fn lit_unset(self, a: &Assignments) -> bool {
        a.0[self.index()] >= 2
    }

    pub fn lit_set(self, a: &Assignments) -> bool {
        a.0[self.index()] < 2
    }

    pub fn to_watchidx(&self) -> usize {
        self.index() * 2 + if self.is_positive() { 0 } else { 1 }
    }
    pub fn to_neg_watchidx(&self) -> usize {
        self.index() * 2 + if self.is_positive() { 1 } else { 0 }
    }

    pub fn phase_saved(idx: usize, assignments: &Assignments) -> Lit {
        Lit {
            idx: idx,
            polarity: if assignments.0[idx] == 1 { true } else { false },
        }
    }

    // This is only called in the parser
    pub fn new(idx: usize, polarity: bool) -> Lit {
        Lit {
            idx: idx,
            polarity: polarity,
        }
    }
}

impl PartialEq for Lit {
    fn eq(&self, other: &Lit) -> bool {
        self.index() == other.index() && self.is_positive() == other.is_positive()
    }
}

impl ops::Not for Lit {
    type Output = Lit;

    #[inline]
    fn not(self) -> Lit {
        Lit { idx: self.index(), polarity: !self.is_positive() }
    }
}
