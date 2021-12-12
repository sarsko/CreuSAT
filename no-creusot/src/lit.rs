use crate::assignments::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Lit {
    pub idx: usize,
    pub polarity: bool,
}

impl Lit {
    // Gets the index of the literal in the representation used for the watchlist
    pub fn to_watchidx(&self) -> usize {
        self.idx * 2 + if self.polarity { 0 } else { 1 }
    }
    // Gets the index of the literal of the opposite polarity(-self) in the representation used for the watchlist
    pub fn to_neg_watchidx(&self) -> usize {
        self.idx * 2 + if self.polarity { 1 } else { 0 }
    }
    pub fn is_sat(&self, assignment: &Assignments) -> bool {
        match assignment.0[self.idx] {
            Some(val) => val == self.polarity,
            None => false,
        }
    }
}