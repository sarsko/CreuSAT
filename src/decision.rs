use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::formula::*;
use crate::lit::*;
use crate::assignments::*;
use crate::util::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    pub next: usize,
    pub prev: usize,
    pub ts: usize,
}

// Todo add bounds check for timestamp
pub struct Decisions {
    //pub lit_order: Vec<usize>,
    //pub loc_of_lit: Vec<usize>,
    pub linked_list: Vec<Node>,
    timestamp: usize,
    pub start: usize,
    pub search: usize,
    //pub head: usize
}

const INVALID: usize = usize::MAX;

impl Decisions {
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
        let mut linked_list = vec::from_elem(Node{ next: INVALID, prev: INVALID, ts: 0 }, f.num_vars);
        i = 0;
        let mut head = 0;
        while i < f.num_vars {
            let j = lit_order[i];
            if i == 0 {
                linked_list[j].next = lit_order[i + 1];
                linked_list[j].prev = INVALID;
                head = j;
            } else if i == f.num_vars - 1 {
                linked_list[j].next = INVALID;
                linked_list[j].prev = lit_order[i - 1];
            } else {
                linked_list[j].next = lit_order[i + 1];
                linked_list[j].prev = lit_order[i - 1];
            }
            linked_list[j].ts = f.num_vars - i;
            i += 1;
        }

        //println!("{:?}", head);
        //println!("{:?}", linked_list[head]);
        Decisions {
            //lit_order: lit_order,
            //loc_of_lit: loc_of_lit,
            linked_list: linked_list,
            timestamp: f.num_vars + 1,
            start: head,
            search: head,
            //head: head,
        }
    }

    fn move_to_front(&mut self, tomove: usize) {
        unsafe {
            if tomove == self.start {
                return;
            }
            let mut moving = &mut self.linked_list.get_unchecked_mut(tomove);
            let prev = moving.prev;
            let old_next = moving.next;
            moving.prev = INVALID;
            moving.next = self.start;
            moving.ts = self.timestamp;
            self.timestamp += 1;
            self.linked_list.get_unchecked_mut(self.start).prev = tomove;
            self.start = tomove;
            self.linked_list.get_unchecked_mut(prev).next = old_next;
            if old_next != INVALID {
                self.linked_list.get_unchecked_mut(old_next).prev = prev;
            }
            /*
            // Why does Satch do this? It should be impossible...?
            if a.0.get_unchecked(tomove) >= &2 {
                panic!();
                self.search = tomove;
            }
            */
        }
    }

    pub fn increment_and_move(&mut self, f: &Formula, cref: usize, a: &Assignments) {
        let clause = &f.clauses[cref];
        let mut counts_with_index = vec![(0, 0); clause.rest.len()];
        let mut i = 0;
        while i < clause.rest.len() {
            counts_with_index[i] = (self.linked_list[clause.rest[i].idx].ts, clause.rest[i].idx);
            i += 1;
        }
        counts_with_index.sort_by_key(|k| k.0);
        i = 0;
        while i < counts_with_index.len() {
            self.move_to_front(counts_with_index[i].1);
            i += 1;
        }
    }

    pub fn get_next(&mut self, a: &Assignments) -> Option<usize> {
        let mut curr = self.search;
        while curr != INVALID {
            unsafe {
                if a.0.get_unchecked(curr) >= &2 {
                    self.search = self.linked_list.get_unchecked(curr).next;
                    return Some(curr);
                }
                curr = self.linked_list.get_unchecked(curr).next;
            }
        }
        return None;
    }
}