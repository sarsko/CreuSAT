use crate::formula::*;
use crate::lit::*;
use crate::assignments::*;

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
        let mut lit_order = vec![0; f.num_vars];
        let mut counts = vec![0; f.num_vars];
        let mut i = 0;  
        while i < f.num_vars {
            let curr_clause = &f.clauses[i];
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
        //println!("{:?}", counts_with_index);
        while i < f.num_vars {
            lit_order[i] = counts_with_index[i].1;
            i += 1;
        }
        let mut linked_list = vec![Node{ next: INVALID, prev: INVALID, ts: 0 }; f.num_vars];
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

    fn move_to_front(&mut self, tomove: usize, a: &Assignments) {
        let mut moving = &mut self.linked_list[tomove];
        let prev = moving.prev;
        if prev == INVALID {
            //assert!(tomove == self.start); 
            return; // We are already head
        }
        let old_next = moving.next;
        moving.prev = INVALID;
        moving.next = self.start;
        moving.ts = self.timestamp;
        self.linked_list[self.start].prev = tomove;
        self.timestamp += 1;
        self.start = tomove;
        self.linked_list[prev].next = old_next;
        if old_next != INVALID {
            self.linked_list[old_next].prev = prev;
        }
        if a.0[tomove] >= 2 {
            self.search = tomove;
        }
    }

    pub fn increment_and_move(&mut self, f: &Formula, cref: usize, a: &Assignments) {
        let clause = &f.clauses[cref];
        let mut i = 0;
        while i < clause.rest.len() && i < 6 {
            self.move_to_front(clause.rest[i].idx, a);
            i += 1;
        }
    }

    pub fn get_next(&mut self, a: &Assignments) -> Option<usize> {
        let mut curr = self.search;
        while curr != INVALID {
            if a.0[curr] >= 2 {
                self.search = curr;
                return Some(curr);
            }
            curr = self.linked_list[curr].next;
        }
        return None;
    }
}