// Watches is Mac OK 11.04 22.13
extern crate creusot_contracts;
use ::std::ops;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{assignments::*, clause::*, trail::*};

#[cfg(feature = "contracts")]
use crate::logic::logic_lit::*;

#[derive(Clone, Copy)]
pub struct Lit {
    pub idx: usize,
    pub polarity: bool,
}

#[cfg(feature = "contracts")]
impl Model for Lit {
    type ModelTy = Lit;

    #[logic]
    fn model(self) -> Self {
        self
    }
}

impl Lit {
    #[inline(always)]
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[ensures(result == self.invariant(@n))]
    pub fn check_lit_invariant(&self, n: usize) -> bool {
        return self.idx < n;
    }

    #[inline(always)]
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[requires(self.invariant((@a).len()))]
    #[ensures(result == self.sat(*a))]
    pub fn lit_sat(self, a: &Assignments) -> bool {
        match self.polarity {
            true => (a.0[self.idx] == 1),
            false => (a.0[self.idx] == 0),
        }
    }

    #[inline(always)]
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[requires(self.invariant((@a).len()))]
    #[ensures(result == self.unsat(*a))]
    pub fn lit_unsat(self, a: &Assignments) -> bool {
        match self.polarity {
            true => (a.0[self.idx] == 0),
            false => (a.0[self.idx] == 1),
        }
    }

    #[inline(always)]
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[requires(self.invariant((@a).len()))]
    #[ensures(result == self.unset(*a))]
    pub fn lit_unset(self, a: &Assignments) -> bool {
        a.0[self.idx] >= 2
    }

    #[inline(always)]
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[requires(self.invariant((@a).len()))]
    #[ensures(result == !self.unset(*a))]
    pub fn lit_set(self, a: &Assignments) -> bool {
        a.0[self.idx] < 2
    }

    // Gets the index of the literal in the representation used for the watchlist
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[requires(@self.idx < @usize::MAX/2)]
    #[ensures(@result == self.to_watchidx_logic())]
    #[ensures(@result == @self.idx * 2 + if self.polarity { 0 } else { 1 })]
    pub fn to_watchidx(&self) -> usize {
        self.idx * 2 + if self.polarity { 0 } else { 1 }
    }
    // Gets the index of the literal of the opposite polarity(-self) in the representation used for the watchlist
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[requires(@self.idx < @usize::MAX/2)]
    #[ensures(@result == self.to_neg_watchidx_logic())]
    #[ensures(@result == @self.idx * 2 + if self.polarity { 1 } else { 0 })]
    pub fn to_neg_watchidx(&self) -> usize {
        self.idx * 2 + if self.polarity { 1 } else { 0 }
    }
}

impl PartialEq for Lit {
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[ensures(result == (self == other))]
    //#[ensures(result == (*self == *other))] // :(
    fn eq(&self, other: &Lit) -> bool {
        self.idx == other.idx && self.polarity == other.polarity
    }
}

impl ops::Not for Lit {
    type Output = Lit;

    #[inline]
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[ensures(@result.idx == @self.idx)]
    #[ensures(result.polarity == !self.polarity)]
    fn not(self) -> Lit {
        Lit { idx: self.idx, polarity: !self.polarity }
    }
}
