use creusot_contracts::{std::*, Clone, Snapshot, *};

use crate::{assignments::*, formula::*, lit::*, solver::*, trail::*};
use ::std::ops::{Index, IndexMut};

#[cfg(creusot)]
use crate::logic::{logic_clause::*, logic_formula::*};

#[derive(Clone)]
pub struct Clause {
    pub deleted: bool,
    pub lbd: u32,
    pub search: usize,
    pub lits: Vec<Lit>, // TODO: unpub
}

impl Index<usize> for Clause {
    type Output = Lit;
    #[inline]
    #[cfg_attr(feature = "trust_clause", trusted)]
    #[requires(ix@ < self@.len())]
    #[ensures(self@[ix@] == *result)]
    fn index(&self, ix: usize) -> &Lit {
        #[cfg(not(creusot))]
        unsafe {
            self.lits.get_unchecked(ix)
        }
        #[cfg(creusot)]
        &self.lits[ix]
    }
}

impl IndexMut<usize> for Clause {
    #[inline]
    #[cfg_attr(feature = "trust_clause", trusted)]
    #[requires(ix@ < self@.len())]
    #[ensures(self@[ix@] == *result)]
    #[ensures((^self)@[ix@] == ^result)]
    #[ensures(forall<i: Int> 0 <= i && i != ix@ && i < self@.len() ==> self@[i] == (^self)@[i])]
    #[ensures((^self)@.len() == (*self)@.len())]
    fn index_mut(&mut self, ix: usize) -> &mut Lit {
        #[cfg(not(creusot))]
        unsafe {
            self.lits.get_unchecked_mut(ix)
        }
        #[cfg(creusot)]
        &mut self.lits[ix]
    }
}

impl Clause {
    #[cfg_attr(feature = "trust_clause", trusted)]
    #[ensures(result == self.inv(n@))]
    pub fn check_clause_invariant(&self, n: usize) -> bool {
        let mut i: usize = 0;
        #[invariant(forall<j: Int> 0 <= j && j < i@ ==> self@[j].inv(n@))]
        while i < self.len() {
            if !self[i].check_lit_invariant(n) {
                return false;
            }
            i += 1;
        }
        return self.no_duplicates();
    }

    #[cfg_attr(feature = "trust_clause", trusted)]
    #[ensures(result == self.no_duplicate_indexes())]
    pub fn no_duplicates(&self) -> bool {
        let mut i: usize = 0;
        #[invariant(
            forall<j: Int, k: Int> 0 <= j && j < i@ &&
             0 <= k && k < j ==> self@[j].index_logic() != self@[k].index_logic())]
        while i < self.len() {
            let lit1 = self[i];
            let mut j: usize = 0;
            #[invariant(forall<k: Int> 0 <= k && k < j@ ==> lit1.index_logic() != self@[k].index_logic())]
            while j < i {
                let lit2 = self[j];
                if lit1.index() == lit2.index() {
                    return false;
                }
                j += 1;
            }
            i += 1;
        }
        true
    }

    #[inline(always)]
    #[cfg_attr(feature = "trust_clause", trusted)]
    #[ensures(result@ == self@.len())]
    pub fn len(&self) -> usize {
        self.lits.len()
    }

    // TODO: Take a look at the parser
    #[inline]
    #[trusted]
    pub fn clause_from_vec(vec: &[Lit]) -> Clause {
        Clause { deleted: false, lbd: 0, search: 2, lits: vec.to_owned() }
    }

    // This does better without splitting
    #[inline(always)]
    #[cfg_attr(feature = "trust_clause", trusted)]
    #[maintains((mut self).inv(_f.num_vars@))]
    #[requires(self@.len() > 0)]
    #[requires(idx@ < self@.len())]
    #[ensures(forall<i: Int> 0 <= i && i < (^self)@.len() ==>
        (exists<j: Int> 0 <= j && j < self@.len() && (^self)@[i] == self@[j]))]
    #[ensures((^self)@[(^self)@.len() - 1] == self@[idx@])]
    #[ensures((^self)@.len() == self@.len())]
    #[ensures(forall<j: Int> 0 <= j && j < self@.len()
        ==> self@[j].lit_in(^self))]
    fn move_to_end(&mut self, idx: usize, _f: &Formula) {
        let end = self.len() - 1;
        self.lits.swap(idx, end);
    }

    // This does better without splitting
    #[inline(always)]
    #[cfg_attr(feature = "trust_clause", trusted)]
    #[maintains((mut self).inv(_f.num_vars@))]
    #[requires(self@.len() > 0)]
    #[requires(idx@ < self@.len())]
    #[ensures(forall<i: Int> 0 <= i && i < (^self)@.len() ==>
        exists<j: Int> 0 <= j && j < self@.len() && (^self)@[i] == self@[j])]
    #[ensures((^self)@.len() + 1 == self@.len())]
    #[ensures(!self@[idx@].lit_in(^self))]
    #[ensures(forall<j: Int> 0 <= j && j < self@.len()
        && j != idx@ ==> self@[j].lit_in(^self))]
    pub fn remove_from_clause(&mut self, idx: usize, _f: &Formula) {
        self.move_to_end(idx, _f);
        self.lits.pop();
    }

    // This is an ugly runtime check
    #[cfg_attr(feature = "trust_clause", trusted)]
    #[requires(inv_internal(self@, _f.num_vars@))]
    #[requires(a.inv(*_f))]
    #[requires(self@.len() > 1)]
    #[ensures(result ==> self.unit(*a))]
    #[ensures(result ==> self@[0].unset(*a))]
    pub fn unit_and_unset(&self, a: &Assignments, _f: &Formula) -> bool {
        let mut i: usize = 1;
        #[invariant(forall<j: Int> 1 <= j && j < i@ ==> self@[j].unsat(*a))]
        while i < self.len() {
            if !self[i].lit_unsat(a) {
                return false;
            }
            i += 1;
        }
        self[0].lit_unset(a)
    }

    // ONLY VALID FOR CLAUSES NOT IN THE FORMULA
    #[cfg_attr(feature = "trust_clause", trusted)]
    #[requires(self@.len() > j@)]
    #[requires(self@.len() > k@)]
    #[requires(_f.inv())]
    #[maintains((mut self).inv(_f.num_vars@))]
    #[maintains((mut self).equisat_extension(*_f))]
    #[ensures(self@.len() == (^self)@.len())]
    #[ensures((^self)@.exchange(self@, j@, k@))]
    pub fn swap_lits_in_clause(&mut self, _f: &Formula, j: usize, k: usize) {
        let old_c: Snapshot<&mut Clause> = snapshot! { self };
        self.lits.swap(j, k);
        proof_assert!(lemma_permuted_clause_maintains_equisat(_f@, *old_c.inner(), *self); true);
        proof_assert!(dup_stable_on_permut(*old_c.inner(), *self); true);
    }

    #[cfg_attr(feature = "trust_clause", trusted)]
    #[requires(t.lit_to_level@.len() == _f.num_vars@)]
    #[requires(self.inv(_f.num_vars@))]
    pub fn calc_lbd(&self, _f: &Formula, s: &mut Solver, t: &Trail) -> usize {
        let mut i: usize = 0;
        let mut lbd: usize = 0;
        #[invariant(lbd@ <= i@)]
        while i < self.len() {
            let level = t.lit_to_level[self[i].index()];
            if level < s.perm_diff.len() && // TODO: Add this as an invariant to Solver
                s.perm_diff[level] != s.num_conflicts
            {
                s.perm_diff[level] = s.num_conflicts;
                lbd += 1;
            }
            i += 1;
        }
        lbd
    }
}
