// Decision is Mac OK 11.04 22.13
extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::{
    formula::*,
    lit::*,
    assignments::*,
    util::{sort_reverse},
};

#[cfg(contracts)]
use crate::logic::{
    logic_util::*,
    logic_decision::*,
};

/*
//#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    pub next: Option<usize>,
    pub prev: Option<usize>,
    pub ts: usize,
}
*/

pub struct Decisions {
    pub lit_order: Vec<usize>,
    /*
    pub linked_list: Vec<Node>,
    timestamp: usize,
    pub start: usize,
    pub head: usize
    */
}

impl Decisions {
    // OK
    #[cfg_attr(all(any(trust_decision, trust_all), not(untrust_all)), trusted)]
    #[requires(f.invariant())]
    #[ensures(result.invariant(@f.num_vars))]
    pub fn new(f: &Formula) -> Decisions {
        let mut lit_order: Vec<usize> = vec::from_elem(0, f.num_vars);
        let mut counts: Vec<usize> = vec::from_elem(0, f.num_vars);
        let mut counts_with_index: Vec<(usize, usize)> = vec::from_elem((0, 0), f.num_vars);
        let mut i: usize = 0;  
        #[invariant(i_bound, @i <= (@f.clauses).len())]
        #[invariant(counts_len1, (@counts).len() == @f.num_vars)]
        while i < f.clauses.len() {
            let curr_clause = &f.clauses[i];
            let mut j: usize = 0;
            #[invariant(i_bound2, @i <= (@f.clauses).len())]
            #[invariant(j_bound, @j <= (@curr_clause.rest).len())]
            #[invariant(counts_len, (@counts).len() == @f.num_vars)]
            while j < curr_clause.rest.len() {
                // Okay this is obviously provable, a vector cannot be longer than usize, and we don't allow duplicates, so we will
                // never overflow, even if every clause contains a literal, 
                if counts[curr_clause.rest[j].idx] < usize::MAX - 1 {
                    counts[curr_clause.rest[j].idx] += 1;
                }
                j += 1;
            }
            i += 1;
        }
        i = 0;
        #[invariant(i_bound, @i <= @f.num_vars)]
        #[invariant(counts_with_idx_len, (@counts_with_index).len() == @f.num_vars)]
        #[invariant(second_ok, forall<j: Int> 0 <= j && j < @f.num_vars ==> 
            @(@counts_with_index)[j].1 < @f.num_vars)]
        while i < f.num_vars {
            counts_with_index[i] = (counts[i], i);
            i += 1;
        }
        sort_reverse(&mut counts_with_index);
        proof_assert!(forall<j: Int> 0 <= j && j < (@counts_with_index).len() ==> 
            @(@counts_with_index)[j].1 < @f.num_vars);
        i = 0;
        #[invariant(i_bound, 0 <= @i && @i <= @f.num_vars)]
        #[invariant(lit_order_len, (@lit_order).len() == @f.num_vars)]
        #[invariant(second_ok, forall<j: Int> 0 <= j && j < @f.num_vars ==> 
            @(@lit_order)[j] < @f.num_vars)]
        while i < f.num_vars {
            lit_order[i] = counts_with_index[i].1;
            i += 1;
        }
        Decisions{lit_order: lit_order}
    }
    /*
    pub fn new(f: &Formula) -> Decisions {
        /*
        let mut lit_order = vec![0; f.num_vars];
        let mut counts = vec![0; f.num_vars];
        let mut i = 0;  
        while i < f.num_vars {
            let curr_clause = &f.clauses[i];
            counts[curr_clause.first.idx] += 1;
            counts[curr_clause.second.idx] += 1;
            let mut j = 0;
            while j < curr_clause.rest.len() {
                counts[curr_clause.rest[j].idx] += 1;
                j += 1;
            }
            i += 1;
        }
        let mut counts_with_index = vec![(0, 0); f.num_vars];
        i = 0;
        while i < f.num_vars {
            counts_with_index[i] = (counts[i], i);
            i += 1;
        }
        counts_with_index.sort_by_key(|k| -k.0);
        i = 0;
        while i < f.num_vars {
            lit_order[i] = counts_with_index[i].1;
            i += 1;
        }
        let mut linked_list = vec![Node{ next: None, prev: None, ts: 0 }; f.num_vars];
        i = 0;
        let mut head = 0;
        while i < f.num_vars {
            let j = lit_order[i];
            if i == 0 {
                linked_list[j].next = Some(lit_order[i + 1]);
                linked_list[j].prev = None;
                head = j;
            } else if i == f.num_vars - 1 {
                linked_list[j].next = None;
                linked_list[j].prev = Some(lit_order[i - 1]);
            } else {
                linked_list[j].next = Some(lit_order[i + 1]);
                linked_list[j].prev = Some(lit_order[i - 1]);
            }
            linked_list[j].ts = f.num_vars - i;
            i += 1;
        }
        Decisions {
            //lit_order: lit_order,
            //loc_of_lit: loc_of_lit,
            linked_list: linked_list,
            timestamp: f.num_vars + 1,
            start: head,
            head: head,
        }
        */
    }
    */

    #[cfg_attr(all(any(trust_decision, trust_all), not(untrust_all)), trusted)]
    fn move_to_front(&mut self, tomove: usize) {
        /*
        let old_next = self.linked_list[tomove].next;
        match self.linked_list[tomove].prev {
            Some(prev) => {
                self.linked_list[prev].next = self.linked_list[tomove].next;
            }
            None => {assert!(tomove == self.start); return;}, // We are already head
        }
        match old_next {
            Some(next) => {
                self.linked_list[next].prev = self.linked_list[tomove].prev;
            }
            None => {},
        }
        self.linked_list[tomove].prev = None;
        self.linked_list[self.start].prev = Some(tomove);
        self.linked_list[tomove].next = Some(self.start);
        self.linked_list[tomove].ts = self.timestamp;
        self.timestamp += 1;
        self.start = tomove;
        */
    }
/*

    #[cfg_attr(all(any(trust_decision, trust_all), not(untrust_all)), trusted)]
    pub fn increment_and_move(&mut self, f: &Formula, cref: usize) {
        let clause = &f.clauses[cref];
        let mut i = 0;
        while i < 8 && i < clause.rest.len() {
            self.move_to_front(clause.rest[i].idx);
            i += 1;
        }
        /*
        let clause = &f.clauses[cref];
        self.move_to_front(clause.first.idx);
        self.move_to_front(clause.second.idx);
        let mut i = 0;
        while i < 3 && i < clause.rest.len() {
            self.move_to_front(clause.rest[i].idx);
            i += 1;
        }
        */
    }
    */

    #[cfg_attr(all(any(trust_decision, trust_all), not(untrust_all)), trusted)]
    pub fn get_next(&mut self, a: &Assignments) -> Option<usize> {
        /*
        let mut head = Some(self.head);
        while head != None {
            if a.0[head.unwrap()] >= 2 {
                self.head = head.unwrap();
                return head;
            }
            head = self.linked_list[head.unwrap()].next;
        }
        */
        return None;
    }
}