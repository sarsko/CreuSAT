use std::{ops, fmt};
use crate::assignments::*;

#[derive(Clone, Copy, Eq, PartialEq, Hash)]
pub struct Lit {
    pub idx: usize,
    pub polarity: bool,
}

impl Lit {
    // Gets the index of the literal in the representation used for the watchlist
    #[inline]
    pub fn to_watchidx(&self) -> usize {
        (self.idx << 1) + if self.polarity { 0 } else { 1 }
    }
    // Gets the index of the literal of the opposite polarity(-self) in the representation used for the watchlist
    #[inline]
    pub fn to_neg_watchidx(&self) -> usize {
        (self.idx << 1) + if self.polarity { 1 } else { 0 }
    }
    #[inline]
    pub fn is_sat(&self, assignment: &Assignments) -> bool {
        assignment.0[self.idx] == self.polarity as u8
    }
}

impl fmt::Debug for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !self.polarity {
            write!(f, "¬")?;
        }
        write!(f, "{:?}", self.idx)
    }
}

impl ops::Not for Lit {
    type Output = Lit;

    #[inline]
    fn not(self) -> Lit {
        Lit {
            idx: self.idx,
            polarity: !self.polarity,
        }
    }
}