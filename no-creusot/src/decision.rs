use crate::assignments::*;
use crate::formula::*;
use crate::lit::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    pub next: Option<usize>,
    pub prev: Option<usize>,
    pub ts: usize,
}

// Todo add bounds check for timestamp
pub struct Decisions {
    //pub lit_order: Vec<usize>,
    //pub loc_of_lit: Vec<usize>,
    pub linked_list: Vec<Node>,
    timestamp: usize,
    pub start: usize,
    pub head: usize,
}

impl Decisions {
    pub fn new(f: &Formula) -> Decisions {
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
        let mut linked_list = vec![
            Node {
                next: None,
                prev: None,
                ts: 0
            };
            f.num_vars
        ];
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
    }

    fn move_to_front(&mut self, tomove: usize) {
        let old_next = self.linked_list[tomove].next;
        match self.linked_list[tomove].prev {
            Some(prev) => {
                self.linked_list[prev].next = self.linked_list[tomove].next;
            }
            None => {
                assert!(tomove == self.start);
                return;
            } // We are already head
        }
        match old_next {
            Some(next) => {
                self.linked_list[next].prev = self.linked_list[tomove].prev;
            }
            None => {}
        }
        self.linked_list[tomove].prev = None;
        self.linked_list[self.start].prev = Some(tomove);
        self.linked_list[tomove].next = Some(self.start);
        self.linked_list[tomove].ts = self.timestamp;
        self.timestamp += 1;
        self.start = tomove;
    }

    pub fn increment_and_move(&mut self, f: &Formula, cref: usize) {
        let clause = &f.clauses[cref];
        self.move_to_front(clause.first.idx);
        self.move_to_front(clause.second.idx);
        let mut i = 0;
        while i < 3 && i < clause.rest.len() {
            self.move_to_front(clause.rest[i].idx);
            i += 1;
        }
    }

    pub fn get_next(&mut self, a: &Assignments) -> Option<usize> {
        let mut head = Some(self.head);
        while head != None {
            if a.0[head.unwrap()] >= 2 {
                self.head = head.unwrap();
                return head;
            }
            head = self.linked_list[head.unwrap()].next;
        }
        return None;
    }
}
