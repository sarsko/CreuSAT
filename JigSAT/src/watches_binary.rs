use crate::{clause::*, formula::*, lit::*, trail::*};
use std::{
    ops::{Index, IndexMut},
};

// From lit to implied lits:
pub struct BinWatches {
    pub watches: Vec<Vec<Lit>>,
}

impl Index<usize> for BinWatches {
    type Output = Vec<Lit>;
    #[inline]
    fn index(&self, i: usize) -> &Vec<Lit> {
        //#[cfg(feature = "unsafe_access")]
        unsafe {
            self.watches.get_unchecked(i)
        }
        //#[cfg(not(feature = "unsafe_access"))]
        //&self.watches[i]
    }
}

impl IndexMut<usize> for BinWatches {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut Vec<Lit> {
        //#[cfg(feature = "unsafe_access")]
        unsafe {
            self.watches.get_unchecked_mut(i)
        }
        //#[cfg(not(feature = "unsafe_access"))]
        //&mut self.watches[i]
    }
}


impl BinWatches {
    pub fn new(f: &Formula) -> BinWatches {
        let mut i: usize = 0;
        let mut watches = Vec::new();
        while i < f.num_vars {
            watches.push(Vec::new());
            watches.push(Vec::new());
            i += 1;
        }
        BinWatches { watches }
    }

    pub fn init_watches(&mut self, f: &Formula) {
        let mut i = 0;
        while i < f.len() {
            let clause = &f[i];
            if clause.len() == 2 {
                self.watches[clause[0].to_neg_watchidx()].push(clause[1]);
                self.watches[clause[1].to_neg_watchidx()].push(clause[0]);
            }
            i += 1;
        }
    }

    pub fn add_watch(&mut self, lit1: Lit, lit2: Lit) {
        self.watches[lit1.to_neg_watchidx()].push(lit2);
        self.watches[lit2.to_neg_watchidx()].push(lit1);
    }

    /* 
    pub fn unwatch(&mut self, f: &Formula, trail: &Trail, cref: usize, lit: Lit) {
        let watchidx = lit.to_neg_watchidx();
        let mut i: usize = 0;
        while i < self.watches[watchidx].len() {
            if self.watches[watchidx][i].cref == cref {
                let end = self.watches[watchidx].len() - 1;
                self.watches[watchidx].swap(i, end);
                match self.watches[watchidx].pop() {
                    Some(w) => {
                    }
                    None => {
                        unreachable!();
                    }
                }
                return;
            }
            i += 1;
        }
    }

    pub fn move_to_end(&mut self, old_idx: usize, old_pos: usize, new_lit: Lit, _f: &Formula) {
        let end = self.watches[old_idx].len() - 1;
        self.watches[old_idx].swap(old_pos, end);
    }


    pub fn unwatch_all_lemmas(&mut self, f: &Formula, s: &Solver) {
        let mut i: usize = 0;
        while i < self.watches.len() {
            let mut j = 0;
            while j < self.watches[i].len() {
                if self.watches[i][j].cref > s.initial_len - 1{
                    let end = self.watches[i].len() - 1;
                    self.watches[i].swap(j, end);
                    self.watches[i].pop();
                } else {
                    j += 1;
                }
            }
            i += 1;
        }
    }
    */
}