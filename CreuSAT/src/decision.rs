extern crate creusot_contracts;
use creusot_contracts::invariant::{Invariant, self};
use creusot_contracts::{*, pearlite, ensures, requires, predicate, trusted, vec};
use ::std::num;
use ::std::ops::{Index, IndexMut};

use crate::assignments::Assignments;
use crate::formula::Formula;

// TODO: Glucose uses 0 for invalid
const INVALID: usize = usize::MAX;

// TODO: Add unsafe indexing for indices and activity as well.
struct Heap {
    activity: Vec<f64>,
    heap: Vec<usize>,
    indices: Vec<usize>,
    num_vars: usize,
}

// TODO: Change all to be some length?
// NOTE: Heap has a manually implemented `Invariant` as it conflicts with `IndexMut` otherwise
impl Heap {
    #[why3::attr = "inline:trivial"]
    #[predicate]
    pub fn invariant(self) -> bool {
        pearlite!{
            self.num_vars@ < 9223372036854775807
            && self.activity@.len() == self.num_vars@
            && self.indices@.len() == self.num_vars@
            && self.heap@.len() <= self.num_vars@
            && forall<i: Int> 0 <= i && i < self.heap@.len() ==> 
               self.heap@[i]@ < self.indices@.len() && self.heap@[i]@ < self.activity@.len()
        }
    }
}

impl Index<usize> for Heap {
    type Output = usize;
    #[inline]
    #[requires(ix@ < self.heap@.len())]
    #[ensures(self.heap@[ix@] == *result)]
    fn index(&self, ix: usize) -> &usize {
        #[cfg(not(creusot))]
        unsafe { self.heap.get_unchecked(ix) }
        #[cfg(creusot)]
        &self.heap[ix]
    }
}

/*
impl IndexMut<usize> for Heap {
    #[inline]
    #[requires(ix@ < self.heap@.len())]
    #[ensures((*self).heap@[ix@] == *result)]
    #[ensures((^self).heap@[ix@] == ^result)]
    #[ensures(forall<i: Int> 0 <= i && i != ix@ && i < self.heap@.len() ==> self.heap@[i] == (^self).heap@[i])]
    #[ensures((^self).heap@.len() == (*self).heap@.len())]
    fn index_mut(&mut self, ix: usize) -> &mut usize {
        #[cfg(not(creusot))]
        unsafe { self.heap.get_unchecked_mut(ix) }
        #[cfg(creusot)]
        &mut self.heap[ix]
    }
}
*/

impl Heap {
    // TODO: This can be simplified, but is blocked on a panic in Creusot
    #[requires(num_vars@ < 9223372036854775807)] // (usize::MAX - 1) / 2
    #[ensures(result.invariant())]
    pub(crate) fn new(num_vars: usize) -> Self {
        let mut heap = Vec::new();
        let mut indices = Vec::new();
        let mut activity = Vec::new();

        // TODO: Swap to for-loop ?
        let mut i = 0;
        #[invariant(activity@.len() == i@)]
        #[invariant(indices@.len() == i@)]
        #[invariant(heap@.len() == i@)]
        #[invariant(forall<i: Int> 0 <= i && i < heap@.len() ==> heap@[i]@ < indices@.len() && heap@[i]@ < activity@.len())]
        #[invariant(i@ <= num_vars@)]
        while i < num_vars {
            indices.push(i);
            heap.push(i);
            activity.push(0.0);
            i += 1;
        }

        let mut heap = Heap { activity, heap, indices, num_vars};

        if num_vars > 1 {
            heap.percolate_all();
        }

        heap
    }

    #[maintains((mut self).invariant())]
    #[requires(self.heap@.len() > 1)]
    #[requires(self.heap@.len() == self.num_vars@)] // This is strictly speaking too strong, but fits our uses
    fn percolate_all(&mut self) {
        let mut i = self.heap.len() / 2 - 1;
        let old_self: Ghost<&mut Self> = ghost!(self);

        #[invariant(old_self.num_vars == self.num_vars)]
        #[invariant(self.invariant())]
        #[invariant(i@ < self.heap@.len())]
        loop {
            self.percolate_down(i);
            if i == 0 {
                break;
            }
            i -= 1;
        }
    }

    /*
    #[requires(n@ < 9223372036854775807)] // (usize::MAX - 1) / 2
    #[ensures(result.invariant())]
    pub(crate) fn new_empty(n: usize) -> Self {
        Heap { activity: vec![0.0; n], heap: Vec::new(), indices: vec![INVALID; n] }
    }
    */

    // TODO: Add. The arguments are wrong, and should take the heap to build from.
    /*
    // Requires a new to have been created with n or larger before
    // TODO: Add support for turning off decision variables (eliminating variables entirely)
    #[maintains((mut self).invariant())]
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
    */


    #[inline(always)] 
    #[requires(idx@ < (usize::MAX@ - 1) / 2)]
    #[ensures(result@ == idx@ * 2 + 1)]
    fn left(idx: usize) -> usize {
        idx * 2 + 1
    }

    #[requires(idx@ < (usize::MAX@ - 1) / 2)]
    #[ensures(result@ == (idx@ + 1) * 2)]
    fn right(idx: usize) -> usize {
        (idx + 1) * 2
    }

    // TODO: Shr not supported
    // TODO: The overflow should be fine when running in release -> it should be fine to have conditional compilation and have Creusot check that.
    #[inline(always)] 
    #[ensures(idx@ == 0 ==> result@ == usize::MAX@)]
    #[ensures(idx@ > 0 ==> result@ == (idx@ - 1) / 2)]
    fn parent(idx: usize) -> usize {
        //(idx - 1) >> 1
        if idx > 0 {
            (idx - 1) / 2
        } else {
           usize::MAX 
        }

    }

    // TODO: Strengthen?
    #[ensures(result == (v@ < self.indices@.len() && self.indices@[v@]@ < self.heap@.len()))]
    fn in_heap(&self, v: usize) -> bool {
        v < self.indices.len() && self.indices[v] < self.heap.len()//self.indices[v] < INVALID
    }

    // TODO: This is going to need a clippy tag thingy
    #[ensures(result == (self.heap@.len() == 0))]
    fn empty(&self) -> bool {
        self.heap.len() == 0
    }

    // TODO strengthen and remove check ?
    #[maintains((mut self).invariant())]
    #[ensures(self.num_vars@ == (^self).num_vars@)]
    //#[requires(v@ < self.indices@.len())]
    fn decrease(&mut self, v: usize) {
        if self.in_heap(v) {
            let idx = self.indices[v];
            self.percolate_up(idx);
        }
    }

    // This is supposed to be used in add_clause
    // TODO strengthen and remove check ?
    #[maintains((mut self).invariant())]
    #[ensures(self.num_vars@ == (^self).num_vars@)]
    //#[requires(v@ < self.indices@.len())]
    fn increase(&mut self, v: usize) {
        if self.in_heap(v) {
            let idx = self.indices[v];
            self.percolate_down(idx);
        }
    }


    // TODO: Add unsafe indexing
    #[inline(always)]
    #[requires(x@ < self.activity@.len())]
    #[requires(y@ < self.activity@.len())]
    fn less_than(&self, x: usize, y: usize) -> bool {
        self.activity[x] > self.activity[y]
    }


    #[maintains((mut self).invariant())]
    #[ensures(self.num_vars@ == (^self).num_vars@)]
    #[requires(self.heap@.len() < self.indices@.len())]
    #[requires(v@ < self.indices@.len())]
    fn insert(&mut self, v: usize) {
        let old_len = self.heap.len();
        self.indices[v] = old_len;
        self.heap.push(v);
        self.percolate_up(old_len);
    }

    // TODO: Swap to unsafe indexing (at least for the reads)
    #[maintains((mut self).invariant())]
    #[ensures(self.num_vars@ == (^self).num_vars@)]
    #[requires(idx@ < self.heap@.len())]
    fn percolate_up(&mut self, mut idx: usize) {
        let x = self[idx];
        let mut p = Self::parent(idx);
        let old_self: Ghost<&mut Self> = ghost!(self);

        #[invariant(self.invariant())]
        #[invariant(idx@ < self.heap@.len())]
        #[invariant(idx@ != 0 ==> p@ < self.heap@.len())]
        #[invariant(x@ < self.activity@.len())]
        #[invariant(old_self.num_vars@ == self.num_vars@)]
        #[invariant(self.heap@.len() == old_self.heap@.len())]
        while idx != 0 && self.less_than(x, self.heap[p]) {
            self.heap[idx] = self[p]; // TODO: Swap to use IndexMut / unsafe. It is for some reason not working
            let i = self.heap[p];
            self.indices[i] = idx;
            idx = p;
            p = Self::parent(idx);
        }

        self.heap[idx] = x;
        self.indices[x] = idx;
    }

    #[requires(idx@ < 9223372036854775807)] // (usize::MAX - 1) / 2
    #[ensures(self.num_vars@ == (^self).num_vars@)]
    #[ensures(self.heap@.len() == (^self).heap@.len())] // This shouldn't be needed (should be got from num_vars remaining unchanged) // Needed for now as we do <= on len
    #[maintains((mut self).invariant())]
    #[requires(idx@ < self.heap@.len())]
    fn percolate_down(&mut self, mut idx: usize) {
        let x = self[idx];
        let old_self: Ghost<&mut Self> = ghost!(self);

        #[invariant(self.invariant())]
        #[invariant(idx@ < self.heap@.len())]
        #[invariant(x@ < self.activity@.len())]
        #[invariant(old_self.num_vars@ == self.num_vars@)]
        #[invariant(self.heap@.len() == old_self.heap@.len())]
        while Self::left(idx) < self.heap.len() {
            let right = Self::right(idx);
            let left = Self::left(idx);
            let child = if right < self.heap.len() && self.less_than(self[right], self[left]) { right } else { left };
            if !self.less_than(self[child], x) {
                break;
            }
            self.heap[idx] = self[child];
            let i = self[idx];
            self.indices[i] = idx;
            idx = child;
        }

        self.heap[idx] = x;
        self.indices[x] = idx;
    }

    #[maintains((mut self).invariant())]
    #[ensures(self.num_vars@ == (^self).num_vars@)]
    #[requires(self.heap@.len() > 0)]
    fn remove_min(&mut self) -> usize {
        let x = self[0];
        self.heap[0] = self.heap[self.heap.len() - 1];
        let first = self[0];
        self.indices[first] = 0;
        self.indices[x] = INVALID;
        self.heap.pop();
        if self.heap.len() > 1 {
            self.percolate_down(0);
        }
        x
    }
}

#[allow(clippy::upper_case_acronyms)]
pub struct Decisions {
    order_heap: Heap,
    var_inc: f64,
    var_decay: f64,
    pub(crate) decision: Vec<bool>,
}

impl Decisions {
    #[predicate]
    pub fn invariant(self, num_vars: Int) -> bool {
        pearlite! {
            self.order_heap.invariant()
            && self.decision@.len() == self.order_heap.num_vars@
            && self.order_heap.num_vars@ == num_vars
        }
    }
}

impl Decisions {
    #[requires(num_vars@ < 9223372036854775807)] // (usize::MAX - 1) / 2
    #[ensures(result.invariant(num_vars@))]
    pub fn new(num_vars: usize) -> Self {
        Self {
            order_heap: Heap::new(num_vars),
            var_inc: 1.0,
            var_decay: 0.95,
            decision: vec![true; num_vars]
        }
    }

    // Has to be called on an non-empty heap
    #[maintains((mut self).invariant(self.order_heap.num_vars@))]
    //#[ensures(self.order_heap.num_vars@ == (^self).order_heap.num_vars@)]
    #[requires(self.order_heap.heap@.len() > 0)]
    pub fn remove_min(&mut self) -> usize {
        self.order_heap.remove_min()
    }

    // TODO
    #[maintains((mut self).invariant(self.order_heap.num_vars@))]
    pub fn get_next(&mut self, a: &Assignments, _f: &Formula) -> Option<usize> {
        /*
        while !self.order_heap.heap.len() == 0 {
            let next = self.remove_min();
            // Don't think the self.decision check really is needed.
            if self.decision[next] && a[next] >= 2 {
                return Some(next);
            }
        }
        */
        None
    }

    #[inline(always)]
    #[maintains((mut self).invariant(self.order_heap.num_vars@))]
    #[ensures(self.order_heap.heap@.len() == (^self).order_heap.heap@.len())]
    //#[ensures(self.order_heap.num_vars == (^self).order_heap.num_vars)]
    #[requires(v@ < self.order_heap.activity@.len())]
    fn rescale(&mut self, v: usize) {
        // Rescale:
        for e in self.order_heap.activity.iter_mut() {
            *e *= 1e-100;
        }
        self.var_inc *= 1e-100;
    }

    //#[maintains((mut self).invariant())]
    #[maintains((mut self).invariant(self.order_heap.num_vars@))]
    #[requires(v@ < self.order_heap.activity@.len())]
    pub fn bump_variable(&mut self, v: usize) {
        self.order_heap.activity[v] += self.var_inc;
        if self.order_heap.activity[v] > 1e100 {
            self.rescale(v);
        }

        // decrease checks whether v is in heap internally
        self.order_heap.decrease(v);
    }

    #[inline(always)]
    #[maintains((mut self).invariant(self.order_heap.num_vars@))]
    pub fn decay_var_inc(&mut self) {
        self.var_inc *= 1.0 / self.var_decay;
    }

    #[inline(always)]
    #[maintains((mut self).invariant(self.order_heap.num_vars@))]
    pub fn set_var_decay(&mut self, new_val: f64) {
        self.var_decay = new_val;
    }


    #[maintains((mut self).invariant(self.order_heap.num_vars@))]
    //#[ensures(self.order_heap.num_vars@ == (^self).order_heap.num_vars@)] // TODO: embed in invariant ?
    #[requires(self.order_heap.heap@.len() < self.order_heap.indices@.len())]
    #[requires(v@ < self.decision@.len())]
    pub fn insert(&mut self, v: usize) {
        if !self.order_heap.in_heap(v) && self.decision[v] {
            self.order_heap.insert(v);
        }
    }

    /*
    #[maintains((mut self).invariant(self.order_heap.num_vars@))]
    pub fn bump_reason_literals(&mut self, var: usize, trail: &Trail, formula: &Formula) {
        let reason = trail.lit_to_reason[var];
        if reason == INVALID {
            return;
        }
        for l in formula.clauses[reason].lits.iter().skip(1) {
            self.bump_variable(l.index());
        }
    }
    */

    #[maintains((mut self).invariant(self.order_heap.num_vars@))]
    #[requires(v@ < self.decision@.len())]
    pub fn turn_off_decision_for_idx(&mut self, v: usize) {
        self.decision[v] = false;
    }
}