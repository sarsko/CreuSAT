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
    #[cfg(feature = "contracts")]
    pub idx: usize,
    #[cfg(not(feature = "contracts"))]
    idx: usize,
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
    #[ensures(@result == self.index_logic())]
    pub fn index(self) -> usize {
        self.idx
    }

    #[inline(always)]
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[ensures(result == self.is_positive_logic())]
    pub fn is_positive(self) -> bool {
        self.polarity
    }

    #[inline(always)]
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[ensures(result == self.invariant(@n))]
    pub fn check_lit_invariant(&self, n: usize) -> bool {
        return self.index() < n;
    }

    #[inline(always)]
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[requires(self.invariant((@a).len()))]
    #[ensures(result == self.sat(*a))]
    pub fn lit_sat(self, a: &Assignments) -> bool {
        match self.polarity {
            true => (a.0[self.index()] == 1),
            false => (a.0[self.index()] == 0),
        }
    }

    #[inline(always)]
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[requires(self.invariant((@a).len()))]
    #[ensures(result == self.unsat(*a))]
    pub fn lit_unsat(self, a: &Assignments) -> bool {
        match self.polarity {
            true => (a.0[self.index()] == 0),
            false => (a.0[self.index()] == 1),
        }
    }

    #[inline(always)]
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[requires(self.invariant((@a).len()))]
    #[ensures(result == self.unset(*a))]
    pub fn lit_unset(self, a: &Assignments) -> bool {
        a.0[self.index()] >= 2
    }

    #[inline(always)]
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[requires(self.invariant((@a).len()))]
    #[ensures(result == !self.unset(*a))]
    pub fn lit_set(self, a: &Assignments) -> bool {
        a.0[self.index()] < 2
    }

    // Gets the index of the literal in the representation used for the watchlist
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[requires(self.index_logic() < @usize::MAX/2)]
    #[ensures(@result == self.to_watchidx_logic())]
    #[ensures(@result == self.index_logic() * 2 + if self.polarity { 0 } else { 1 })]
    pub fn to_watchidx(&self) -> usize {
        self.index() * 2 + if self.polarity { 0 } else { 1 }
    }
    // Gets the index of the literal of the opposite polarity(-self) in the representation used for the watchlist
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[requires(self.index_logic() < @usize::MAX/2)]
    #[ensures(@result == self.to_neg_watchidx_logic())]
    #[ensures(@result == self.index_logic() * 2 + if self.polarity { 1 } else { 0 })]
    pub fn to_neg_watchidx(&self) -> usize {
        self.index() * 2 + if self.polarity { 1 } else { 0 }
    }

    #[requires(@idx < (@assignments).len())]
    #[ensures(result.index_logic() == @idx)]
    #[ensures(result.is_positive_logic() == (@(@assignments)[@idx] == 1))]
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
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[ensures(result == (self == other))]
    //#[ensures(result == (*self == *other))] // :(
    fn eq(&self, other: &Lit) -> bool {
        self.index() == other.index() && self.polarity == other.polarity
    }
}

impl ops::Not for Lit {
    type Output = Lit;

    #[inline]
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[ensures(result.index_logic() == self.index_logic())]
    #[ensures(result.polarity == !self.polarity)]
    fn not(self) -> Lit {
        Lit { idx: self.index(), polarity: !self.polarity }
    }
}
