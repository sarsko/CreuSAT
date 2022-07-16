use crate::{assignments::*, formula::*, trail::*, util::*};
use std::ops::{Index, IndexMut};

const INVALID: usize = usize::MAX;
pub(crate) trait Decisions {
    fn new(f: &Formula) -> Self
    where
        Self: Sized;

    fn bump_vec_of_vars(&mut self, f: &Formula, v: Vec<usize>);

    fn bump_reason_literals(&mut self, var: usize, trail: &Trail, formula: &Formula);

    fn get_next(&mut self, a: &Assignments, _f: &Formula) -> Option<usize>;

    fn bump_variable(&mut self, var: usize);

    fn decay_var_inc(&mut self);

    fn set_var_decay(&mut self, new_val: f64);

    fn insert(&mut self, var: usize);

    fn turn_off_decision_for_idx(&mut self, var: usize);
}

#[derive(Clone, Copy)]
pub(crate) struct Node {
    pub next: usize,
    pub prev: usize,
    pub ts: usize,
}

impl Default for Node {
    fn default() -> Self {
        Node { next: usize::MAX, prev: usize::MAX, ts: 0 }
    }
}

pub(crate) struct VMTF {
    pub linked_list: Vec<Node>,
    timestamp: usize,
    pub start: usize,
    pub search: usize,
}

impl Index<usize> for VMTF {
    type Output = Node;
    #[inline]
    fn index(&self, i: usize) -> &Node {
        //#[cfg(feature = "unsafe_access")]
        unsafe { self.linked_list.get_unchecked(i) }
        //#[cfg(not(feature = "unsafe_access"))]
        //&self.linked_list[i]
    }
}

impl IndexMut<usize> for VMTF {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut Node {
        //#[cfg(feature = "unsafe_access")]
        unsafe { self.linked_list.get_unchecked_mut(i) }
        //#[cfg(not(feature = "unsafe_access"))]
        //&mut self.linked_list[i]
    }
}

impl VMTF {
    fn make_linked_list(f: &Formula, lit_order: Vec<usize>) -> VMTF {
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
        VMTF { linked_list, timestamp: f.num_vars + 1, start: head, search: head }
    }

    fn rescore(&mut self, _f: &Formula) {
        let mut curr_score = self.linked_list.len();
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
        //let mut moving = &mut self.linked_list[tomove];
        let mut moving = unsafe { self.linked_list.get_unchecked_mut(tomove) };
        let prev = moving.prev;
        let old_next = moving.next;
        moving.prev = INVALID;
        moving.next = self.start;
        moving.ts = self.timestamp;
        self.linked_list[self.start].prev = tomove;
        self.start = tomove;
        unsafe {
            self.linked_list.get_unchecked_mut(prev).next = old_next;
        }
        if old_next != INVALID {
            unsafe {
                self.linked_list.get_unchecked_mut(old_next).prev = prev;
            }
        }
        if self.timestamp == usize::MAX {
            self.rescore(_f);
        } else {
            self.timestamp += 1;
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

impl Decisions for VMTF {
    fn new(f: &Formula) -> VMTF {
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

    fn bump_vec_of_vars(&mut self, f: &Formula, v: Vec<usize>) {
        let mut counts_with_index: Vec<(usize, usize)> = vec![(0, 0); v.len()];
        let mut i: usize = 0;
        while i < v.len() {
            counts_with_index[i] = (self.linked_list[v[i]].ts, v[i]);
            i += 1;
        }
        // TODO: Check actual speed. I believe selection sort is the slowest. Only need permut property.
        //insertion_sort(&mut counts_with_index);
        //sort(&mut counts_with_index);
        // Better sort seems yield a few percentages lol
        //counts_with_index.sort_unstable();
        counts_with_index.sort_unstable_by_key(|k| k.0);
        i = 0;
        while i < counts_with_index.len() {
            self.move_to_front(counts_with_index[i].1, f);
            i += 1;
        }
    }

    fn get_next(&mut self, a: &Assignments, _f: &Formula) -> Option<usize> {
        let mut curr = self.search;
        while curr != INVALID {
            if a[curr] >= 2 {
                self.search = self[curr].next;
                return Some(curr);
            }
            curr = self[curr].next;
        }
        let mut i: usize = 0;
        while i < a.len() {
            if a[i] >= 2 {
                panic!();
            }
            i += 1;
        }
        None
    }

    // TODO: Add decision toggling for VMTF.
    fn turn_off_decision_for_idx(&mut self, var: usize) {}

    // No-op, but may add to see.
    fn bump_reason_literals(&mut self, var: usize, trail: &Trail, formula: &Formula) {}

    // This is a no-op, as VMTF only support bumping of vecs of vars.
    fn bump_variable(&mut self, var: usize) {}

    // No-ops
    fn decay_var_inc(&mut self) {}

    fn set_var_decay(&mut self, new_val: f64) {}

    fn insert(&mut self, var: usize) {}
}

struct Heap {
    activity: Vec<f64>,
    heap: Vec<usize>,
    indices: Vec<usize>,
}

impl Index<usize> for Heap {
    type Output = usize;
    #[inline]
    fn index(&self, i: usize) -> &usize {
        //#[cfg(feature = "unsafe_access")]
        unsafe { self.heap.get_unchecked(i) }
        //#[cfg(not(feature = "unsafe_access"))]
        //&self.lits[i]
    }
}

impl IndexMut<usize> for Heap {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut usize {
        //#[cfg(feature = "unsafe_access")]
        unsafe { self.heap.get_unchecked_mut(i) }
        //#[cfg(not(feature = "unsafe_access"))]
        //&mut self.lits[i]
    }
}

impl Default for Heap {
    fn default() -> Self {
        Heap { activity: Vec::new(), heap: Vec::new(), indices: Vec::new() }
    }
}

impl Heap {
    pub(crate) fn new(n: usize) -> Self {
        Heap { activity: vec![0.0; n], heap: Vec::new(), indices: vec![INVALID; n] }
    }

    // Requires a new to have been created with n or larger before
    // TODO: Add support for turning off decision variables (eliminating variables entirely)
    pub(crate) fn build(&mut self, n: usize) {
        if n == 0 {
            return;
        }

        for e in &self.heap {
            self.indices[*e] = INVALID;
        }
        self.heap.clear();

        for i in 0..n {
            self.indices[i] = i;
            self.heap.push(i);
        }

        if n == 1 {
            return;
        }

        let mut i = self.len() / 2 - 1;
        loop {
            self.percolate_down(i);
            if i == 0 {
                break;
            }
            i -= 1;
        }
    }

    fn left(idx: usize) -> usize {
        idx * 2 + 1
    }

    fn right(idx: usize) -> usize {
        (idx + 1) * 2
    }

    fn parent(idx: usize) -> usize {
        (idx - 1) >> 1
    }

    fn len(&self) -> usize {
        self.heap.len()
    }

    fn in_heap(&self, var: usize) -> bool {
        var < self.indices.len() && self.indices[var] < INVALID
    }

    fn empty(&self) -> bool {
        self.heap.len() == 0
    }

    fn decrease(&mut self, var: usize) {
        self.percolate_up(self.indices[var]);
    }

    fn increase(&mut self, var: usize) {
        self.percolate_down(self.indices[var]);
    }

    #[inline(always)]
    fn less_than(&self, x: usize, y: usize) -> bool {
        self.activity[x] > self.activity[y]
    }

    fn insert(&mut self, var: usize) {
        assert!(var < self.indices.len());
        self.indices[var] = self.len();
        self.heap.push(var);
        self.percolate_up(self.indices[var]);
    }

    fn percolate_up(&mut self, mut idx: usize) {
        let x = self[idx];
        let mut p = Self::parent(idx);

        while idx != 0 && self.less_than(x, self[p]) {
            self[idx] = self[p];
            let i = self[p];
            self.indices[i] = idx;
            idx = p;
            p = Self::parent(idx);
        }
        self[idx] = x;
        self.indices[x] = idx;
    }

    fn percolate_down(&mut self, mut idx: usize) {
        let x = self[idx];

        while Self::left(idx) < self.len() {
            let right = Self::right(idx);
            let left = Self::left(idx);
            let child = if right < self.len() && self.less_than(self[right], self[left]) { right } else { left };
            if !self.less_than(self[child], x) {
                break;
            }
            self[idx] = self[child];
            let i = self[idx];
            self.indices[i] = idx;
            idx = child;
        }
        self[idx] = x;
        self.indices[x] = idx;
    }

    fn remove_min(&mut self) -> usize {
        let x = self[0];
        self[0] = *self.heap.last().unwrap();
        let first = self[0];
        self.indices[first] = 0;
        self.indices[x] = INVALID;
        self.heap.pop();
        if self.len() > 1 {
            self.percolate_down(0);
        }
        x
    }
}

pub(crate) struct VSIDS {
    order_heap: Heap,
    var_inc: f64,
    var_decay: f64,
    pub(crate) decision: Vec<bool>,
}

impl Default for VSIDS {
    fn default() -> Self {
        VSIDS { order_heap: Heap::default(), var_inc: 1.0, var_decay: 0.95, decision: Vec::new() }
    }
}

impl VSIDS {
    fn empty(&self) -> bool {
        self.order_heap.empty()
    }

    // Has to be called on an non-empty heap
    fn remove_min(&mut self) -> usize {
        self.order_heap.remove_min()
    }
}

impl Decisions for VSIDS {
    fn new(formula: &Formula) -> Self {
        let mut vsids = VSIDS::default();
        vsids.order_heap = Heap::new(formula.num_vars);
        vsids.order_heap.build(formula.num_vars);
        vsids.decision = vec![true; formula.num_vars];
        vsids
    }

    fn get_next(&mut self, a: &Assignments, _f: &Formula) -> Option<usize> {
        while !self.empty() {
            let next = self.remove_min();
            // Don't think the self.decision check really is needed.
            if self.decision[next] && a[next] >= 2 {
                return Some(next);
            }
        }
        None
    }

    fn bump_variable(&mut self, var: usize) {
        self.order_heap.activity[var] += self.var_inc;
        if self.order_heap.activity[var] > 1e100 {
            // Rescale:
            for e in self.order_heap.activity.iter_mut() {
                *e *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }

        if self.order_heap.in_heap(var) {
            self.order_heap.decrease(var);
        }
    }

    fn decay_var_inc(&mut self) {
        self.var_inc *= 1.0 / self.var_decay;
    }

    fn set_var_decay(&mut self, new_val: f64) {
        self.var_decay = new_val;
    }

    fn insert(&mut self, var: usize) {
        if !self.order_heap.in_heap(var) && self.decision[var] {
            self.order_heap.insert(var);
        }
    }

    fn bump_reason_literals(&mut self, var: usize, trail: &Trail, formula: &Formula) {
        let reason = trail.lit_to_reason[var];
        if reason == INVALID {
            return;
        }
        let clause = &formula[reason];
        for l in formula.clauses[reason].lits.iter().skip(1) {
            self.bump_variable(l.index());
        }
    }

    fn turn_off_decision_for_idx(&mut self, var: usize) {
        self.decision[var] = false;
    }

    // Deliberately a no-op
    fn bump_vec_of_vars(&mut self, f: &Formula, v: Vec<usize>) {}
}

/*
impl Decisions {
    pub(crate) fn new(formula: &Formula) -> Self {
        Decisions { vsids: VSIDS::new(formula) }
    }

    pub(crate) fn get_next(&mut self, a: &Assignments, _f: &Formula) -> Option<usize> {
        while !self.vsids.empty() {
            let next = self.vsids.remove_min();
            if a[next] >= 2 {
                return Some(next);
            }
        }
        None
    }

    pub(crate) fn bump_variable(&mut self, var: usize) {
        self.vsids.bump_variable(var);
    }

    pub(crate) fn decay_var_inc(&mut self) {
        self.vsids.decay_var_inc();
    }

    pub(crate) fn set_var_decay(&mut self, new_val: f64) {
        self.vsids.set_var_decay(new_val);
    }

    pub(crate) fn insert(&mut self, var: usize) {
        self.vsids.insert(var);
    }
}

*/
