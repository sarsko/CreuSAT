extern crate creusot_contracts;
use creusot_contracts::logic::Ghost;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{assignments::*, formula::*, trail::*, util::*};
use ::std::ops::{Index, IndexMut};

// #[cfg(feature = "contracts")]
//use crate::logic::{logic::unset, logic_decision::*, logic_util::*};

struct Heap {
    activity: Vec<f64>,
    heap: Vec<usize>,
    indices: Vec<usize>,
}

impl Index<usize> for Heap {
    type Output = usize;
    #[inline]
    #[cfg_attr(feature = "trust_decisions", trusted)]
    #[requires(@ix < (@self.heap).len())]
    #[ensures((@self.heap)[@ix] == *result)]
    fn index(&self, ix: usize) -> &usize {
        #[cfg(not(feature = "contracts"))]
        unsafe {
            self.heap.get_unchecked(ix)
        }
        #[cfg(feature = "contracts")]
        &self.heap[ix]
    }
}

impl IndexMut<usize> for Heap {
    #[inline]
    #[cfg_attr(feature = "trust_decisions", trusted)]
    #[requires(@ix < (@self.heap).len())]
    #[ensures((@self.heap)[@ix] == *result)]
    #[ensures((@(^self).heap)[@ix] == ^result)]
    #[ensures(forall<i : Int> 0 <= i && i != @ix && i < (@self.heap).len() ==> (@self.heap)[i] == (@(^self).heap)[i])]
    #[ensures((@(^self).heap).len() == (@self.heap).len())]
    fn index_mut(&mut self, ix: usize) -> &mut usize {
        #[cfg(not(feature = "contracts"))]
        unsafe { self.heap.get_unchecked_mut(ix) }
        #[cfg(feature = "contracts")]
        &mut self.heap[ix]
    }
}

impl Default for Heap {
    fn default() -> Self {
        Heap { activity: Vec::new(), heap: Vec::new(), indices: Vec::new() }
    }
}

impl Heap {
    pub(crate) fn new(n: usize) -> Self {
        //let activity_default: f64 = 0.0; // Creusot issue #163
        let act_vec = vec::from_elem(f64::default(), n);
        Heap { activity: act_vec, heap: Vec::new(), indices: vec::from_elem(usize::MAX, n) }
    }

    // Requires a new to have been created with n or larger before
    // TODO: Add support for turning off decision variables (eliminating variables entirely)
    pub(crate) fn build(&mut self, n: usize) {
        if n == 0 {
            return;
        }

        for e in &self.heap {
            self.indices[*e] = usize::MAX;
        }
        self.heap.clear();

        let mut i:usize  = 0;
        while i < n {
            self.indices[i] = i;
            self.heap.push(i);
            i += 1;
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
        (idx - 1 ) / 2
        //(idx - 1) >> 1
    }

    fn len(&self) -> usize {
        self.heap.len()
    }

    fn in_heap(&self, var: usize) -> bool {
        var < self.indices.len() && self.indices[var] < usize::MAX
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
        self.indices[x] = usize::MAX;
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
    #[trusted] // Needs trusted to circumvent Creusot error
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

impl VSIDS {
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
        let one_e_hundred = 1e100;
        let one_e_minus_hundred = 1e-100;
        if self.order_heap.activity[var] > one_e_hundred {
            // Rescale:
            for e in self.order_heap.activity.iter_mut() {
                *e *= one_e_minus_hundred;
            }
            self.var_inc *= one_e_minus_hundred;
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
        if reason == usize::MAX {
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