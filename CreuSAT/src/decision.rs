use creusot_contracts::{ensures, invariant, maintains, proof_assert, requires, std::vec, Clone, Int, Snapshot, *};

use crate::{assignments::*, formula::*, util::*};

#[cfg(creusot)]
use crate::logic::{logic::unset, logic_decision::*, logic_util::*};

#[derive(Clone, Copy)]
pub struct Node {
    pub next: usize,
    pub prev: usize,
    pub ts: usize,
}

const INVALID: usize = usize::MAX;

impl ::std::default::Default for Node {
    #[ensures(result.next@ == usize::MAX@)]
    #[ensures(result.prev@ == usize::MAX@)]
    #[ensures(result.ts@   == 0)]
    fn default() -> Self {
        Node { next: usize::MAX, prev: usize::MAX, ts: 0 }
    }
}

impl creusot_contracts::Default for Node {
    #[predicate]
    #[open]
    fn is_default(self) -> bool {
        pearlite! { self.next@ == usize::MAX@ && self.prev@ == usize::MAX@ && self.ts@ == 0 }
    }
}

pub struct Decisions {
    pub linked_list: Vec<Node>,
    timestamp: usize,
    pub start: usize,
    pub search: usize,
}

impl Decisions {
    // It is possible to sacrifice some readability for a tad faster proofs here(by adding assertions).
    #[cfg_attr(feature = "trust_decision", trusted)]
    #[requires(f.inv())]
    #[requires(0 < f.num_vars@ && f.num_vars@ < usize::MAX@/2)]
    #[requires(lit_order@.len() == f.num_vars@ &&
            forall<i: Int> 0 <= i && i < lit_order@.len() ==>
                lit_order@[i]@ < f.num_vars@)]
    #[ensures(result.inv(f.num_vars@))]
    pub fn make_linked_list(f: &Formula, lit_order: Vec<usize>) -> Decisions {
        let mut linked_list: Vec<Node> = vec::from_elem(Node::default(), f.num_vars);
        let mut i: usize = 0;
        let mut head: usize = 0;
        #[invariant(linked_list@.len() == f.num_vars@)]
        #[invariant(head@ < f.num_vars@)]
        #[invariant(forall<j: Int> 0 <= j && j < f.num_vars@ ==>
                ((linked_list@[j].next@ == usize::MAX@ || linked_list@[j].next@ < f.num_vars@)
                && (linked_list@[j].prev@ == usize::MAX@ || linked_list@[j].prev@ < f.num_vars@)))]
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

    #[cfg_attr(feature = "trust_decision", trusted)]
    #[requires(f.inv())]
    #[requires(0 < f.num_vars@ && f.num_vars@ < usize::MAX@/2)]
    #[ensures(result.inv(f.num_vars@))]
    pub fn new(f: &Formula) -> Decisions {
        let mut lit_order: Vec<usize> = vec::from_elem(0, f.num_vars);
        let mut counts: Vec<usize> = vec::from_elem(0, f.num_vars);
        let mut counts_with_index: Vec<(usize, usize)> = vec::from_elem((0, 0), f.num_vars);
        let mut i: usize = 0;
        #[invariant(i@ <= f.clauses@.len())]
        #[invariant(counts@.len() == f.num_vars@)]
        while i < f.clauses.len() {
            let curr_clause = &f[i];
            let mut j: usize = 0;
            #[invariant(i@ <= f.clauses@.len())]
            #[invariant(j@ <= curr_clause@.len())]
            #[invariant(counts@.len() == f.num_vars@)]
            while j < curr_clause.len() {
                // Okay this is obviously provable, a vector cannot be longer than usize, and we don't allow duplicates, so we will
                // never overflow, even if every clause contains a literal,
                if counts[curr_clause[j].index()] < usize::MAX - 1 {
                    counts[curr_clause[j].index()] += 1;
                }
                j += 1;
            }
            i += 1;
        }
        i = 0;
        #[invariant(i@ <= f.num_vars@)]
        #[invariant(counts_with_index@.len() == f.num_vars@)]
        #[invariant(forall<j: Int> 0 <= j && j < f.num_vars@ ==> counts_with_index@[j].1@ < f.num_vars@)]
        while i < f.num_vars {
            counts_with_index[i] = (counts[i], i);
            i += 1;
        }
        sort_reverse(&mut counts_with_index);
        proof_assert!(forall<j: Int> 0 <= j && j < counts_with_index@.len() ==> counts_with_index@[j].1@ < f.num_vars@);
        i = 0;
        #[invariant(0 <= i@ && i@ <= f.num_vars@)]
        #[invariant(lit_order@.len() == f.num_vars@)]
        #[invariant(forall<j: Int> 0 <= j && j < f.num_vars@ ==> lit_order@[j]@ < f.num_vars@)]
        while i < f.num_vars {
            lit_order[i] = counts_with_index[i].1;
            i += 1;
        }
        Self::make_linked_list(f, lit_order)
    }

    #[cfg_attr(feature = "trust_decision", trusted)]
    #[maintains((mut self).inv(_f.num_vars@))]
    #[requires(self.linked_list@.len() < usize::MAX@)]
    #[ensures((^self).timestamp@ == self.linked_list@.len() + 1)]
    #[ensures((^self).linked_list@.len() == self.linked_list@.len())]
    fn rescore(&mut self, _f: &Formula) {
        let old_self: Snapshot<&mut Decisions> = snapshot! { self };
        let mut curr_score = self.linked_list.len();
        let mut i: usize = 0;
        let mut curr = self.start;
        #[invariant(curr == usize::MAX || curr@ < self.linked_list@.len())]
        #[invariant(forall<j: Int> 0 <= j && j < self.linked_list@.len() ==>
            (self.linked_list@[j].next == old_self.linked_list@[j].next
            && self.linked_list@[j].prev == old_self.linked_list@[j].prev)
        )]
        #[invariant(self.inv(_f.num_vars@))]
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

    #[cfg_attr(feature = "trust_decision", trusted)]
    #[requires(_f.num_vars@ < usize::MAX@)]
    #[requires(tomove@ < self.linked_list@.len())]
    #[maintains((mut self).inv(_f.num_vars@))]
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
        proof_assert!(self.start@ < _f.num_vars@);
        self.linked_list[self.start].prev = tomove;
        self.start = tomove;
        if prev != INVALID {
            // lazy, should prove
            self.linked_list[prev].next = old_next;
        }
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

    #[cfg_attr(feature = "trust_decision", trusted)]
    #[requires(elems_less_than(v@, f.num_vars@))]
    #[requires(f.num_vars@ < usize::MAX@)]
    #[requires(f.inv())]
    #[maintains((mut self).inv(f.num_vars@))]
    pub fn increment_and_move(&mut self, f: &Formula, v: Vec<usize>) {
        let mut counts_with_index: Vec<(usize, usize)> = vec![(0, 0); v.len()];
        let old_self: Snapshot<&mut Decisions> = snapshot! { self };
        let mut i: usize = 0;
        #[invariant(old_self.inner() == self)]
        #[invariant(v@.len() == counts_with_index@.len())]
        #[invariant(forall<j: Int> 0 <= j && j < i@ ==> counts_with_index@[j].1@ < self.linked_list@.len())]
        while i < v.len() {
            counts_with_index[i] = (self.linked_list[v[i]].ts, v[i]);
            i += 1;
        }
        // TODO: Check actual speed. I believe selection sort is the slowest. Only need permut property.
        //insertion_sort(&mut counts_with_index);
        sort(&mut counts_with_index);
        //counts_with_index.sort_unstable_by_key(|k| k.0);
        //counts_with_index.sort_by_key(|k| k.0);
        i = 0;
        #[invariant(self.inv(f.num_vars@))]
        #[invariant(v@.len() == counts_with_index@.len())]
        while i < counts_with_index.len() {
            self.move_to_front(counts_with_index[i].1, f);
            i += 1;
        }
    }

    // SAREK TODO
    #[cfg_attr(feature = "trust_decision", trusted)]
    #[maintains((mut self).inv(_f.num_vars@))]
    #[requires(a.inv(*_f))]
    #[ensures(match result {
        Some(k) => k@ < (a@).len() && unset((a@)[k@]),
        None    => a.complete(),
    })]
    pub fn get_next(&mut self, a: &Assignments, _f: &Formula) -> Option<usize> {
        let mut curr = self.search;
        #[invariant(curr == usize::MAX || curr@ < (a@).len())]
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
        #[invariant(forall<j: Int> 0 <= j && j < i@ ==> !unset((a@)[j]))]
        while i < a.len() {
            if a[i] >= 2 {
                return Some(i);
            }
            i += 1;
        }
        None
    }
}
