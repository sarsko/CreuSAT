extern crate creusot_contracts;
use creusot_contracts::*;
//use creusot_contracts::std::*;

//use std::{ops, fmt};
use std::ops;
use crate::assignments::*;

//#[derive(Clone, Copy, Eq, PartialEq, Hash)]
#[derive(Clone, Copy)]
pub struct Lit {
    pub idx: usize,
    pub polarity: bool,
}

#[logic]
#[requires(0 <= n && @l.idx < n)]
#[ensures(l.to_neg_watchidx_logic() < 2 * n)]
#[ensures(l.to_watchidx_logic() < 2 * n)]
pub fn lemma_watchidx_less(l: Lit, n: Int) {}

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
    #[trusted] // OK
    #[requires(@self.idx < @usize::MAX/2)]
    #[ensures(@result === self.to_watchidx_logic())]
    #[ensures(@result === @self.idx * 2 + if self.polarity { 0 } else { 1 })]
    pub fn to_watchidx(&self) -> usize {
        self.idx * 2 + if self.polarity { 0 } else { 1 }
    }
    // Gets the index of the literal of the opposite polarity(-self) in the representation used for the watchlist
    #[trusted] // OK
    #[requires(@self.idx < @usize::MAX/2)]
    #[ensures(@result === self.to_neg_watchidx_logic())]
    #[ensures(@result === @self.idx * 2 + if self.polarity { 1 } else { 0 })]
    pub fn to_neg_watchidx(&self) -> usize {
        self.idx * 2 + if self.polarity { 1 } else { 0 }
    }

    //#[inline]
    #[trusted] // OK
    #[requires(@self.idx < (@assignments).len())]
    #[ensures(result === ((@(@assignments)[@self.idx] === 1 && self.polarity) || (@(@assignments)[@self.idx] === 0 && !self.polarity)))]
    /*
    #[ensures(match ((@(@assignments)[@self.idx]), self.polarity) {
                (1, true) => result,
                (0, false) => result,
                _ => !result,
    })]
    */
    pub fn is_sat(&self, assignments: &Assignments) -> bool {
        /*
        if self.polarity {
            return assignments.0[self.idx] == 1;
        } else {
            return assignments.0[self.idx] == 0;
        }
        */
        match (assignments.0[self.idx], self.polarity) {
            (1, true) => true,
            (0, false) => true,
            _ => false,
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
    #[trusted] // OK
    #[ensures(@result.idx === @self.idx)]
    #[ensures(result.polarity === !self.polarity)]
    fn not(self) -> Lit {
        Lit {
            idx: self.idx,
            polarity: !self.polarity,
        }
    }
}