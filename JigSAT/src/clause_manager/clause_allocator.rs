use crate::lit::{Lit, ClauseHeader};
use crate::clause_manager::common::{CRef, HEADER_LEN};

use std::{
    cmp::Ordering,
    ops::{Index, IndexMut},
};

pub(crate) struct ClauseAllocator {
    buffer: Vec<Lit>,
}

impl ClauseAllocator {
    pub fn new() -> Self {
        ClauseAllocator { buffer: Vec::new() }
    }

    pub(crate) fn add_clause(&mut self, lits: &[Lit]) -> CRef {
        let cref = self.buffer.len() as CRef;
        self.buffer.push(Lit::raw(lits.len() as u32));
        self.buffer.push(Lit::calc_header(lits));

        for lit in lits {
            self.buffer.push(*lit);
        }

        cref
    }

    pub(crate) fn add_clause_parser(&mut self, lits: &[Lit]) -> CRef {
        let cref = self.buffer.len() as CRef;
        self.buffer.push(Lit::raw(lits.len() as u32));
        self.buffer.push(Lit::calc_header_parser(lits));

        for lit in lits {
            self.buffer.push(*lit);
        }

        cref
    }

    pub(crate) fn get_clause(&self, cref: CRef) -> &[Lit] {
        let idx = cref as usize;
        let len = self.buffer[idx].get_raw() as usize;
        &self.buffer[idx + HEADER_LEN..idx + HEADER_LEN + len]
    }

    pub(crate) fn get_clause_mut(&mut self, cref: CRef) -> &mut [Lit] {
        let idx = cref as usize;
        let len = self.buffer[idx].get_raw() as usize;
        &mut self.buffer[idx + HEADER_LEN..idx + HEADER_LEN + len]
    }

    pub(crate) fn get_clause_header(&mut self, cref: CRef) -> ClauseHeader {
        let idx = cref as usize;
        let out = ClauseHeader(&mut self.buffer[idx..idx + HEADER_LEN]);
        assert!(out.0.len() == 2);
        out
    }

    pub(crate) fn get_first_lit(&self, cref: CRef) -> Lit {
        self.buffer[cref as usize + HEADER_LEN]
    }

    pub(crate) fn get_second_lit(&self, cref: CRef) -> Lit {
        self.buffer[cref as usize + HEADER_LEN + 1]
    }

    pub(crate) fn get_lit(&self, cref: CRef) -> Lit {
        self.buffer[cref as usize]
    }

    pub(crate) fn get_lit_mut(&mut self, cref: CRef) -> &mut Lit {
        &mut self.buffer[cref as usize]
    }

    #[inline(always)]
    pub(crate) fn get_len(&self, cref: CRef) -> u32 {
        self.buffer[cref as usize].get_raw()
    }

    // TODO: Refactor in clause manager to use this
    #[inline(always)]
    pub(crate) fn get_lbd(&self, cref: CRef) -> u16 {
        self.buffer[cref as usize + 1].get_lbd()
    }

    pub(crate) fn clause_less_than(&self, a: CRef, b: CRef) -> Ordering {
        let a_len = self.get_len(a);
        let b_len = self.get_len(b);
        if a_len == 2 {
            if b_len == 2 {
                Ordering::Equal
            } else {
                Ordering::Less
            }
        } else if b_len == 2 {
            Ordering::Greater
        } else {
            let a_lbd = self.get_lbd(a);
            let b_lbd = self.get_lbd(b);
            if a_lbd < b_lbd {
                Ordering::Less
            } else if a_lbd > b_lbd {
                Ordering::Greater
            } else if a_len < b_len {
                Ordering::Less 
            } else if a_len > b_len {
                Ordering::Greater
            } else {
                Ordering::Equal
            }
        }
    }
}