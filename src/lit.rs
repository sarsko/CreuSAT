extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use ::std::ops;

use crate::{
    assignments::*,
    clause::*,
    trail::*,
};

#[cfg(contracts)]
use crate::logic::{
    logic_lit::*,
};

#[derive(Clone, Copy)]
//#[derive(Clone, Copy, Debug)]
pub struct Lit {
    pub idx: usize,
    pub polarity: bool,
}


impl Lit {
    #[trusted] // OK
    #[inline(always)]
    #[requires(self.invariant((@a).len()))]
    #[ensures(result === self.sat(*a))]
    pub fn lit_sat(self, a: &Assignments) -> bool {
        match self.polarity {
            true  =>  (a.0[self.idx] == 1),
            false =>  (a.0[self.idx] == 0),
        }
    }

    #[trusted] // OK
    #[inline(always)]
    #[requires(self.invariant((@a).len()))]
    #[ensures(result === self.unsat(*a))]
    pub fn lit_unsat(self, a: &Assignments) -> bool {
        match self.polarity {
            true  =>  (a.0[self.idx] == 0),
            false =>  (a.0[self.idx] == 1),
        }
    }

    #[trusted] // OK
    #[inline(always)]
    #[requires(self.invariant((@a).len()))]
    #[ensures(result === self.unset(*a))]
    pub fn lit_unset(self, a: &Assignments) -> bool {
        a.0[self.idx] >= 2
    }
    
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
}

impl PartialEq for Lit {
    #[trusted] // OK
    #[ensures(result === (*self === *other))]
    fn eq(&self, other: &Lit) -> bool {
        self.idx == other.idx && self.polarity == other.polarity
    } 
}

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