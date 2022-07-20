use ::std::ops;

use crate::assignments::*;

#[derive(Clone, Copy, Eq, PartialEq, PartialOrd, Ord)]
pub struct Lit {
    code: u32,
}

pub(crate) const ZERO_LIT: Lit = Lit { code: 0 };

use std::fmt;

impl fmt::Debug for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}
impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let neg_or_empty = if self.is_positive() { "" } else { "¬" };
        write!(f, "{}   {}", neg_or_empty, self.index())
    }
}

impl Lit {
    #[inline(always)]
    pub fn index(self) -> usize {
        (self.code >> 1) as usize
    }

    /*
    #[inline(always)]
    pub fn var(self) -> Var {
        self.code >> 1
    }
    */

    #[inline(always)]
    pub fn is_positive(self) -> bool {
        self.code & 1 != 0
    }

    #[inline(always)]
    pub fn check_lit_invariant(self, n: usize) -> bool {
        self.index() < n
    }

    #[inline(always)]
    pub fn lit_sat(self, a: &Assignments) -> bool {
        a[self.index()] == self.is_positive() as u8
    }

    #[inline(always)]
    pub fn lit_unsat(self, a: &Assignments) -> bool {
        a[self.index()] == !self.is_positive() as u8
    }

    #[inline(always)]
    pub fn lit_unset(self, a: &Assignments) -> bool {
        a[self.index()] >= 2
    }

    #[inline(always)]
    pub fn lit_set(self, a: &Assignments) -> bool {
        a[self.index()] < 2
    }

    #[inline(always)]
    pub fn get_curr_assigned_state(self, a: &Assignments) -> AssignedState {
        a[self.index()]
    }

    #[inline(always)]
    pub fn to_watchidx(self) -> usize {
        self.code as usize
    }
    #[inline(always)]
    pub fn to_neg_watchidx(self) -> usize {
        (!self).code as usize
    }

    // This is only called in the parser
    pub fn new(idx: usize, polarity: bool) -> Lit {
        Lit { code: (idx << 1) as u32 | (polarity as u32) }
    }

    #[inline]
    pub fn select_other(self, a: Self, b: Self) -> Self {
        Self { code: self.code ^ a.code ^ b.code }
    }

    #[inline]
    pub(crate) fn abstract_level(self, t: &Vec<u32>) -> u32 {
        1 << (t[self.index()] & 31)
    }

    #[inline]
    pub(crate) fn lit_in_clause(self, c: &[Lit]) -> bool {
        for l in c {
            if *l == self {
                return true;
            }
        }
        false
    }
}

impl ops::Not for Lit {
    type Output = Lit;

    #[inline]
    fn not(self) -> Lit {
        Lit { code: self.code ^ 1 }
    }
}

/*
HEADER:
deleted: 1
can_be_deleted: 1
mark: 2
lbd: 28 // This is more than needed, and may be reduced in the future
*/

//const DELETED_ON: u32  = 0b11111111111111111111111111111111u32;
const DELETED_ON: u32 = 0b1000_0000_0000_0000_0000_0000_0000_0000u32;
const DELETED_OFF: u32 = !DELETED_ON; // 0b01111111111111111111111111111111u32;

const CAN_BE_DELETED_ON: u32 = 0b01000000000000000000000000000000u32;
const CAN_BE_DELETED_OFF: u32 = !CAN_BE_DELETED_ON;

const LBD_BITS: u32 = 0b00001111111111111111111111111111u32;

// HEADER STUFF
impl Lit {
    pub(crate) fn raw(code: u32) -> Self {
        Self { code }
    }

    pub(crate) fn set_deleted(&mut self) {
        self.code |= DELETED_ON;
    }

    pub(crate) fn unset_deleted(&mut self) {
        self.code &= DELETED_OFF;
    }

    pub(crate) fn to_be_deleted(&self) -> bool {
        self.code >= DELETED_ON
    }

    pub(crate) fn set_can_be_deleted(&mut self) {
        self.code |= CAN_BE_DELETED_ON;
    }

    pub(crate) fn unset_can_be_deleted(&mut self) {
        self.code &= DELETED_OFF
    }

    pub(crate) fn can_be_deleted(&self) -> bool {
        self.code | CAN_BE_DELETED_ON == self.code
    }

    // REQUIRES self to be zeroes in the LBD range
    pub(crate) fn set_fresh_lbd(&mut self, new_val: u32) {
        // Wipes upper bits and sets code
        self.code |= new_val & LBD_BITS
    }

    // REQUIRES self to be a header lit
    pub(crate) fn get_lbd(&self) -> u32 {
        // Wipes upper bits and sets code
        self.code & LBD_BITS
    }

    // Requires that this is an header lit
    // Ugly name to prevent misuse.
    pub(crate) fn get_len_from_header_lit(&self) -> u32 {
        self.code
    }
}
