use crate::{assignments::*, formula::*, util::*};

#[derive(Clone, Copy)]
pub struct Node {
    pub next: usize,
    pub prev: usize,
    pub ts: usize,
}

const INVALID: usize = usize::MAX;

impl Default for Node {
    fn default() -> Self {
        Node { next: usize::MAX, prev: usize::MAX, ts: 0 }
    }
}

pub struct Decisions {
    pub linked_list: Vec<Node>,
    timestamp: usize,
    pub start: usize,
    pub search: usize,
}


impl Decisions {
    pub fn make_linked_list(f: &Formula, lit_order: Vec<usize>) -> Decisions {
        let mut linked_list: Vec<Node> = vec![Default::default(); f.num_vars];
        let mut i: usize = 0;
        let mut head: usize = 0;
        while i < f.num_vars {
            let j = lit_order[i];
            if i == 0 {
                if f.num_vars > 1 {
                    linked_list[j].next = lit_order[1];
                } else {
                    linked_list[j].next = INVALID;
                }
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
        Decisions { linked_list: linked_list, timestamp: f.num_vars + 1, start: head, search: head }
    }

    pub fn new(f: &Formula) -> Decisions {
        let mut lit_order: Vec<usize> = vec![0; f.num_vars];
        let mut counts: Vec<usize> = vec![0; f.num_vars];
        let mut counts_with_index: Vec<(usize, usize)> = vec![(0, 0); f.num_vars];
        let mut i: usize = 0;
        while i < f.len() {
            let curr_clause = &f[i];
            let mut j: usize = 0;
            while j < curr_clause.len() {
                counts[curr_clause[j].index()] += 1;
                j += 1;
            }
            i += 1;
        }
        i = 0;
        while i < f.num_vars {
            counts_with_index[i] = (counts[i], i);
            i += 1;
        }
        sort_reverse(&mut counts_with_index);
        i = 0;
        while i < f.num_vars {
            lit_order[i] = counts_with_index[i].1;
            i += 1;
        }
        Self::make_linked_list(f, lit_order)
    }

    fn rescore(&mut self, _f: &Formula) {
        let mut curr_score = self.linked_list.len();
        let mut i: usize = 0;
        let mut curr = self.start;
        while curr != INVALID {
            self.linked_list[curr].ts = curr_score;
            if curr_score > 0 {
                curr_score -= 1;
            } else {
                break;
            }
            curr = self.linked_list[curr].next;
        }
        self.timestamp = self.linked_list.len() + 1;
    }

    fn move_to_front(&mut self, tomove: usize, _f: &Formula) {
        if tomove == self.start {
            return;
        }
        let mut moving = &mut self.linked_list[tomove];
        let prev = moving.prev;
        let old_next = moving.next;
        moving.prev = INVALID;
        moving.next = self.start;
        moving.ts = self.timestamp;
        if self.timestamp == usize::MAX {
            self.rescore(_f);
        } else {
            self.timestamp += 1;
        }
        self.linked_list[self.start].prev = tomove;
        self.start = tomove;
        self.linked_list[prev].next = old_next;
        if old_next != INVALID {
            self.linked_list[old_next].prev = prev;
        }
        /*
        // Why does Satch do this? It should be impossible...?
        if a.0.get_unchecked(tomove) >= &2 {
            panic!();
            self.search = tomove;
        }
        */
    }

    pub fn increment_and_move(&mut self, f: &Formula, cref: usize, a: &Assignments) {
        let clause = &f[cref];
        let mut counts_with_index: Vec<(usize, usize)> = vec![(0, 0); clause.len()];
        let mut i: usize = 0;
        while i < clause.len() {
            counts_with_index[i] = (self.linked_list[clause[i].index()].ts, clause[i].index());
            i += 1;
        }
        // TODO: Check actual speed. I believe selection sort is the slowest. Only need permut property.
        //insertion_sort(&mut counts_with_index);
        //sort(&mut counts_with_index);
        // Better sort seems yield a few percentages lol
        //counts_with_index.sort_unstable();
        counts_with_index.sort_by_key(|k| k.0);
        i = 0;
        while i < counts_with_index.len() {
            self.move_to_front(counts_with_index[i].1, f);
            i += 1;
        }
    }

    pub fn get_next(&mut self, a: &Assignments, _f: &Formula) -> Option<usize> {
        let mut curr = self.search;
        while curr != INVALID {
            if a[curr] >= 2 {
                self.search = self.linked_list[curr].next;
                return Some(curr);
            }
            curr = self.linked_list[curr].next;
        }
        // Strictly speaking this is an unecessary runtime check, but it only gets run at most once and it
        // greatly simplifies the proof.
        let mut i: usize = 0;
        while i < a.len() {
            if a[i] >= 2 {
                panic!();
                return Some(i);
            }
            i += 1;
        }
        return None;
    }
}
