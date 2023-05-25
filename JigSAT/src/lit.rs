use ::std::ops;

use crate::assignments::*;

#[derive(Clone, Copy, Eq, PartialEq, PartialOrd, Ord)]
pub struct Lit {
    code: u32,
}

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
    // This is only called in the parser
    /// Creates an encoded `Lit` from the `idx` and `polarity`
    #[inline(always)]
    pub fn new(idx: usize, polarity: bool) -> Lit {
        Lit { code: (idx << 1) as u32 | (polarity as u32) }
    }

    #[inline(always)]
    /// Creates a "raw" `Lit` where the given `code` is used directly
    /// This is intended to be used to store the clause headers
    pub fn raw(code: u32) -> Lit {
        Lit { code }
    }

    #[inline(always)]
    pub fn get_raw(&self) -> u32 {
        self.code
    }


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

    #[allow(unused)]
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

    #[inline]
    pub fn select_other(self, a: Self, b: Self) -> Self {
        Self { code: self.code ^ a.code ^ b.code }
    }

    #[inline]
    pub(crate) fn abstract_level(self, t: &[u32]) -> u32 {
        1 << (t[self.index()] & 31)
    }

    #[inline]
    pub(crate) fn lit_in_clause(self, clause: &[Lit]) -> bool {
        for lit in clause {
            if *lit == self {
                return true;
            }
        }
        false
    }

    // TODO
    pub(crate) fn calc_header(clause: &[Lit]) -> Self {
        Lit { code: 0 }
    }

    // TODO
    pub(crate) fn calc_header_parser(clause: &[Lit]) -> Self {
        Lit { code: 0 }
    }

    // ASSUMES lbd not set
    pub(crate) fn set_lbd(&mut self, lbd: u16) {
        self.code += lbd as u32;
    }
    
    pub(crate) fn get_lbd(&self) -> u16 {
        ((self.code << 16) >> 16) as u16
    }
    
    pub(crate) fn set_search(&mut self, search: u8) {
        let mut asbytes = self.code.to_le_bytes();
        asbytes[3] = search;
        self.code = u32::from_le_bytes(asbytes);
    }
    
    pub(crate) fn get_search(&self) -> u8 {
        self.code.to_le_bytes()[3]
    }

}

impl ops::Not for Lit {
    type Output = Lit;

    #[inline]
    fn not(self) -> Lit {
        Lit { code: self.code ^ 1 }
    }
}

pub(crate) struct ClauseHeader<'a>(pub &'a mut[Lit]);

const CAN_BE_DEL_BIT: u8 = 17;
const IS_DELETED_BIT: u8 = 18;

fn get_bit_at(input: u32, n: u8) -> bool {
    input & (1 << n) != 0
}

impl<'a> ClauseHeader<'a> {
    pub(crate) fn get_len(&self) -> u32 {
        self.0[0].code
    }

    pub(crate) fn get_lbd(&self) -> u16 {
        ((self.0[1].code << 16) >> 16) as u16
    }

    pub(crate) fn can_be_deleted(&self) -> bool {
        get_bit_at(self.0[1].code, CAN_BE_DEL_BIT)
    }

    pub(crate) fn set_can_be_deleted(&mut self) {
        self.0[1].code |= 1 << CAN_BE_DEL_BIT;
    }

    pub(crate) fn mark_clause_as_deleted(&mut self) {
        self.0[1].code |= 1 << IS_DELETED_BIT;
    }
}


