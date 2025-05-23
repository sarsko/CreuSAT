use ::std::ops;
use creusot_contracts::{model::*, std::*, *};

use creusot_contracts::Clone;

use crate::assignments::*;

#[cfg(creusot)]
use crate::logic::logic_lit::*;

#[derive(Clone, Copy)]
pub struct Lit {
    pub idx: usize,
    pub polarity: bool,
}

#[cfg(creusot)]
impl View for Lit {
    type ViewTy = Lit;

    #[logic]
    #[open]
    fn view(self) -> Self {
        self
    }
}

#[cfg(creusot)]
impl DeepModel for Lit {
    type DeepModelTy = Lit;

    #[logic]
    #[open]
    fn deep_model(self) -> Self {
        self
    }
}

impl Lit {
    #[inline(always)]
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[ensures(result@ == self.index_logic())]
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
    #[ensures(result == self.inv(n@))]
    pub fn check_lit_invariant(&self, n: usize) -> bool {
        self.index() < n
    }

    #[inline(always)]
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[requires(self.inv(a@.len()))]
    #[ensures(result == self.sat(*a))]
    pub fn lit_sat(self, a: &Assignments) -> bool {
        match self.is_positive() {
            true => (a[self.index()] == 1),
            false => (a[self.index()] == 0),
        }
    }

    #[inline(always)]
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[requires(self.inv(a@.len()))]
    #[ensures(result == self.unsat(*a))]
    pub fn lit_unsat(self, a: &Assignments) -> bool {
        match self.is_positive() {
            true => (a[self.index()] == 0),
            false => (a[self.index()] == 1),
        }
    }

    #[inline(always)]
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[requires(self.inv(a@.len()))]
    #[ensures(result == self.unset(*a))]
    pub fn lit_unset(self, a: &Assignments) -> bool {
        a[self.index()] >= 2
    }

    #[inline(always)]
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[requires(self.inv(a@.len()))]
    #[ensures(result == !self.unset(*a))]
    pub fn lit_set(self, a: &Assignments) -> bool {
        a[self.index()] < 2
    }

    // Gets the index of the literal in the representation used for the watchlist
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[requires(self.index_logic() < usize::MAX@/2)]
    #[ensures(result@ == self.to_watchidx_logic())]
    #[ensures(result@ == self.index_logic() * 2 + if self.is_positive_logic() { 0 } else { 1 })]
    pub fn to_watchidx(self) -> usize {
        self.index() * 2 + if self.is_positive() { 0 } else { 1 }
    }
    // Gets the index of the literal of the opposite polarity(-self) in the representation used for the watchlist
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[requires(self.index_logic() < usize::MAX@/2)]
    #[ensures(result@ == self.to_neg_watchidx_logic())]
    #[ensures(result@ == self.index_logic() * 2 + if self.is_positive_logic() { 1 } else { 0 })]
    pub fn to_neg_watchidx(self) -> usize {
        self.index() * 2 + if self.is_positive() { 1 } else { 0 }
    }

    #[cfg_attr(feature = "trust_lit", trusted)]
    #[requires(idx@ < assignments@.len())]
    #[ensures(result.index_logic() == idx@)]
    #[ensures(result.is_positive_logic() == (assignments@[idx@]@ == 1))]
    pub fn phase_saved(idx: usize, assignments: &Assignments) -> Lit {
        Lit { idx: idx, polarity: if assignments[idx] == 1 { true } else { false } }
    }

    // This is only called in the parser
    pub fn new(idx: usize, polarity: bool) -> Lit {
        Lit { idx: idx, polarity: polarity }
    }
}

impl PartialEq for Lit {
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[ensures(result == (self == other))]
    //#[ensures(result == (*self == *other))] // :(
    fn eq(&self, other: &Lit) -> bool {
        self.index() == other.index() && self.is_positive() == other.is_positive()
    }
}

impl ops::Not for Lit {
    type Output = Lit;

    #[inline]
    #[cfg_attr(feature = "trust_lit", trusted)]
    #[ensures(result.index_logic() == self.index_logic())]
    #[ensures(result.is_positive_logic() == !self.is_positive_logic())]
    fn not(self) -> Lit {
        Lit { idx: self.index(), polarity: !self.is_positive() }
    }
}
