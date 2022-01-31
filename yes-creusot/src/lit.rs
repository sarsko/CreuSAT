extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

//use std::{ops, fmt};
use std::ops;
use crate::assignments::*;

//#[derive(Clone, Copy, Eq, PartialEq, Hash)]
#[derive(Clone, Copy)]
pub struct Lit {
    pub idx: usize,
    pub polarity: bool,
}

impl Lit {
    #[logic]
    pub fn to_watchidx_logic(&self) -> Int {
        pearlite! { @self.idx * 2 + if self.polarity { 0 } else { 1 } }
    }

    #[logic]
    pub fn to_neg_watchidx_logic(&self) -> Int {
        pearlite! { @self.idx * 2 + if self.polarity { 1 } else { 0 } }
    }
}

impl Lit {
    // Gets the index of the literal in the representation used for the watchlist
    #[requires(@self.idx < @usize::MAX/2)]
    #[ensures(@result === self.to_watchidx_logic())]
    #[ensures(@result === @self.idx * 2 + if self.polarity { 0 } else { 1 })]
    pub fn to_watchidx(&self) -> usize {
        self.idx * 2 + if self.polarity { 0 } else { 1 }
    }
    // Gets the index of the literal of the opposite polarity(-self) in the representation used for the watchlist
    #[requires(@self.idx < @usize::MAX/2)]
    #[ensures(@result === self.to_neg_watchidx_logic())]
    #[ensures(@result === @self.idx * 2 + if self.polarity { 1 } else { 0 })]
    pub fn to_neg_watchidx(&self) -> usize {
        self.idx * 2 + if self.polarity { 1 } else { 0 }
    }

    #[requires(@self.idx < (@assignment).len())]
    pub fn is_sat(&self, assignment: &Assignments) -> bool {
        match assignment.0[self.idx] {
            Some(val) => val == self.polarity,
            None => false,
        }
    }
}

/*
#[trusted]
impl fmt::Debug for Lit {

    #[trusted]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !self.polarity {
            write!(f, "¬")?;
        }
        write!(f, "{:?}", self.idx)
    }
}
*/
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