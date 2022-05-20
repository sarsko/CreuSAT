extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{assignments::*, formula::*, lit::*, util::*};

#[cfg(feature = "contracts")]
use crate::logic::{logic::unset, logic_decision::*, logic_util::*};

//#[derive(Debug, Clone, PartialEq, Eq)]
#[derive(Clone, Copy)]
pub struct Node {
    pub next: usize,
    pub prev: usize,
    pub ts: usize,
}

//const INVALID: usize = usize::MAX;

impl Default for Node {
    #[ensures(@result.next === @usize::MAX)]
    #[ensures(@result.prev === @usize::MAX)]
    #[ensures(@result.ts   === 0)]
    fn default() -> Self { Node { next: usize::MAX, prev: usize::MAX, ts: 0 } }
}

pub struct Decisions {
    pub linked_list: Vec<Node>,
    timestamp: usize,
    pub start: usize,
    pub search: usize,
}

//pub const INVALID: usize = usize::MAX;

impl Decisions {
    // It is possible to sacrifice some readability for a tad faster proofs here(by adding assertions).
    #[cfg_attr(feature = "trust_decision", trusted)]
    #[requires(f.invariant())]
    #[requires(0 < @f.num_vars && @f.num_vars < @usize::MAX/2)]
    #[requires((@lit_order).len() === @f.num_vars &&
            forall<i: Int> 0 <= i && i < (@lit_order).len() ==>
                @(@lit_order)[i] < @f.num_vars)]
    #[ensures(result.invariant(@f.num_vars))]
    pub fn make_linked_list(f: &Formula, lit_order: Vec<usize>) -> Decisions {
        let INVALID: usize = usize::MAX;
        let mut linked_list: Vec<Node> = vec::from_elem(Default::default(), f.num_vars);
        let mut i: usize = 0;
        let mut head: usize = 0;
        #[invariant(len_ok, (@linked_list).len() == @f.num_vars)]
        #[invariant(head_ok, @head < @f.num_vars)]
        #[invariant(inv, forall<j: Int> 0 <= j && j < @f.num_vars ==>
                ((@(@linked_list)[j].next == @usize::MAX || @(@linked_list)[j].next < @f.num_vars)
                && (@(@linked_list)[j].prev == @usize::MAX || @(@linked_list)[j].prev < @f.num_vars)))]
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
    #[requires(f.invariant())]
    #[requires(0 < @f.num_vars && @f.num_vars < @usize::MAX/2)]
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
        Self::make_linked_list(f, lit_order)
    }

    #[cfg_attr(feature = "trust_decision", trusted)]
    #[maintains((mut self).invariant(@_f.num_vars))]
    #[requires((@self.linked_list).len() < @usize::MAX)]
    #[ensures(@(^self).timestamp === (@self.linked_list).len() + 1)]
    #[ensures((@(^self).linked_list).len() === (@self.linked_list).len())]
    fn rescore(&mut self, _f: &Formula) {
        let INVALID: usize = usize::MAX;
        let old_self = Ghost::record(&self);
        let mut curr_score = self.linked_list.len();
        let mut i: usize = 0;
        let mut curr = self.start;
        #[invariant(curr_ok, curr == usize::MAX || @curr < (@self.linked_list).len())]
        #[invariant(proph, ^@old_self === ^self)]
        #[invariant(unch, forall<j: Int> 0 <= j && j < (@self.linked_list).len() ==>
            ((@self.linked_list)[j].next === (@(@old_self).linked_list)[j].next
            && (@self.linked_list)[j].prev === (@(@old_self).linked_list)[j].prev)
        )]
        #[invariant(inv, self.invariant(@_f.num_vars))]
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
    #[requires(@_f.num_vars < @usize::MAX)]
    #[requires(@tomove < (@self.linked_list).len())]
    #[maintains((mut self).invariant(@_f.num_vars))]
    fn move_to_front(&mut self, tomove: usize, _f: &Formula) {
        let INVALID: usize = usize::MAX;
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
        proof_assert!(@self.start < (@_f.num_vars));
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
    #[requires(@f.num_vars < @usize::MAX)]
    #[requires(f.invariant())]
    #[requires(a.invariant(*f))]
    #[requires(@cref < (@f.clauses).len())]
    #[maintains((mut self).invariant(@f.num_vars))]
    pub fn increment_and_move(&mut self, f: &Formula, cref: usize, a: &Assignments) {
        let clause = &f.clauses[cref];
        let mut counts_with_index: Vec<(usize, usize)> = vec::from_elem((0, 0), clause.rest.len());
        let old_self = Ghost::record(&self);
        let mut i: usize = 0;
        #[invariant(unch, @old_self === self)]
        #[invariant(proph, ^@old_self === ^self)]
        #[invariant(len_same, (@clause).len() === (@counts_with_index).len())]
        #[invariant(all_less, forall<j: Int> 0 <= j && j < @i ==>
            @(@counts_with_index)[j].1 < (@self.linked_list).len()
        )]
        while i < clause.rest.len() {
            counts_with_index[i] = (self.linked_list[clause.rest[i].idx].ts, clause.rest[i].idx);
            i += 1;
        }
        // TODO: Check actual speed. I believe selection sort is the slowest. Only need permut property.
        //insertion_sort(&mut counts_with_index);
        sort(&mut counts_with_index);
        //counts_with_index.sort_by_key(|k| k.0);
        i = 0;
        #[invariant(proph, ^@old_self === ^self)]
        #[invariant(inv, self.invariant(@f.num_vars))]
        #[invariant(len_same, (@clause).len() === (@counts_with_index).len())]
        while i < counts_with_index.len() {
            self.move_to_front(counts_with_index[i].1, f);
            i += 1;
        }
    }

    #[cfg_attr(feature = "trust_decision", trusted)]
    #[maintains((mut self).invariant(@_f.num_vars))]
    #[requires(a.invariant(*_f))]
    #[ensures(match result {
        Some(k) => @k < (@a).len() && unset((@a)[@k]),
        None    => a.complete(),
    })]
    pub fn get_next(&mut self, a: &Assignments, _f: &Formula) -> Option<usize> {
        let INVALID: usize = usize::MAX;
        let mut curr = self.search;
        #[invariant(inv, curr == usize::MAX || @curr < (@a).len())]
        while curr != INVALID {
            if a.0[curr] >= 2 {
                self.search = self.linked_list[curr].next;
                return Some(curr);
            }
            curr = self.linked_list[curr].next;
        }
        // Strictly speaking this is an unecessary runtime check, but it only gets run at most once and it
        // greatly simplifies the proof.
        let mut i: usize = 0;
        #[invariant(prev, forall<j: Int> 0 <= j && j < @i ==> !unset((@a)[j]))]
        while i < a.0.len() {
            if a.0[i] >= 2 {
                return Some(i);
            }
            i += 1;
        }
        return None;
    }
}
