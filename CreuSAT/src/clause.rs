extern crate creusot_contracts;
use creusot_contracts::logic::Ghost;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{assignments::*, formula::*, lit::*, solver::*, trail::*};

#[cfg(feature = "contracts")]
use crate::logic::{logic_clause::*, logic_formula::*};

pub struct Clause {
    pub deleted: bool,
    pub lbd: u32,
    pub search: usize,
    pub rest: Vec<Lit>,
}

// Split up invariant and at least binary and revert to
// old invariant instead of invariant_unary_ok

impl Clone for Clause {
    // Will do last
    #[trusted] // TODO
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        Clause { deleted: self.deleted, lbd: self.lbd, search: self.search, rest: self.rest.clone() }
    }
}

impl Clause {
    #[cfg_attr(feature = "trust_clause", trusted)]
    #[ensures(result == self.invariant(@n))]
    pub fn check_clause_invariant(&self, n: usize) -> bool {
        let mut i: usize = 0;
        #[invariant(inv, forall<j: Int> 0 <= j && j < @i ==> (@self)[j].invariant(@n))]
        while i < self.len() {
            if !self.rest[i].check_lit_invariant(n) {
                return false;
            }
            i += 1;
        }
        if self.no_duplicates() {
            return true;
        }
        false
    }

    #[cfg_attr(feature = "trust_clause", trusted)]
    #[ensures(result == self.no_duplicate_indexes())]
    pub fn no_duplicates(&self) -> bool {
        let mut i: usize = 0;
        #[invariant(no_dups,
            forall<j: Int, k: Int> 0 <= j && j < @i &&
             0 <= k && k < j ==> (@self)[j].index_logic() != (@self)[k].index_logic())]
        while i < self.rest.len() {
            let lit1 = self.rest[i];
            let mut j: usize = 0;
            #[invariant(inv, forall<k: Int> 0 <= k && k < @j ==> lit1.index_logic() != (@self)[k].index_logic())]
            while j < i {
                let lit2 = self.rest[j];
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
    #[ensures(@result == (@self).len())]
    pub fn len(&self) -> usize {
        self.rest.len()
    }

    // TODO: Take a look at the parser
    #[inline]
    #[trusted]
    pub fn clause_from_vec(vec: &[Lit]) -> Clause {
        Clause { deleted: false, lbd: 0, search: 1, rest: vec.to_owned() }
    }

    // This does better without splitting
    #[inline(always)]
    #[cfg_attr(feature = "trust_clause", trusted)]
    #[maintains((mut self).invariant_unary_ok(@_f.num_vars))]
    #[requires((@self).len() > 0)]
    #[requires(@idx < (@self).len())]
    #[ensures(forall<i: Int> 0 <= i && i < (@(^self)).len() ==>
        (exists<j: Int> 0 <= j && j < (@self).len() && (@(^self))[i] == (@self)[j]))]
    #[ensures(forall<i: Int> 0 <= i && i < (@(self)).len() ==>
        (exists<j: Int> 0 <= j && j < (@(^self)).len() && (@(^self))[i] == (@self)[j]))]
    #[ensures((@(^self))[(@^self).len() - 1] == (@self)[@idx])]
    #[ensures((@(^self)).len() == (@self).len())]
    #[ensures(forall<j: Int> 0 <= j && j < (@self).len()
        ==> (@self)[j].lit_in(^self))]
    fn move_to_end(&mut self, idx: usize, _f: &Formula) {
        let end = self.rest.len() - 1;
        self.rest.swap(idx, end);
    }

    // This does better without splitting
    #[inline(always)]
    #[cfg_attr(feature = "trust_clause", trusted)]
    #[maintains((mut self).invariant_unary_ok(@_f.num_vars))]
    #[requires((@self).len() > 0)]
    #[requires(@idx < (@self).len())]
    #[ensures(forall<i: Int> 0 <= i && i < (@(^self)).len() ==>
        exists<j: Int> 0 <= j && j < (@self).len() && (@(^self))[i] == (@self)[j])]
    #[ensures((@(^self)).len() + 1 == (@self).len())]
    #[ensures(!(@self)[@idx].lit_in(^self))]
    #[ensures(forall<j: Int> 0 <= j && j < (@self).len()
        && j != @idx ==> (@self)[j].lit_in(^self))]
    pub fn remove_from_clause(&mut self, idx: usize, _f: &Formula) {
        let old_self = ghost! { self };
        self.move_to_end(idx, _f);
        self.rest.pop();
        proof_assert!(^self == ^old_self.inner());
    }

    // This is an ugly runtime check
    #[cfg_attr(feature = "trust_clause", trusted)]
    #[requires(invariant_internal(@self, @_f.num_vars))]
    #[requires(a.invariant(*_f))]
    #[requires((@self).len() > 1)]
    #[ensures(result ==> self.unit(*a))]
    #[ensures(result ==> (@self)[0].unset(*a))]
    pub fn unit_and_unset(&self, a: &Assignments, _f: &Formula) -> bool {
        let mut i: usize = 1;
        #[invariant(unsat, forall<j: Int> 1 <= j && j < @i ==> (@self)[j].unsat(*a))]
        while i < self.rest.len() {
            if !self.rest[i].lit_unsat(a) {
                return false;
            }
            i += 1;
        }
        self.rest[0].lit_unset(a)
    }

    // ONLY VALID FOR CLAUSES NOT IN THE FORMULA
    #[cfg_attr(feature = "trust_clause", trusted)]
    #[requires((@self).len() > @j)]
    #[requires((@self).len() > @k)]
    #[maintains((mut self).invariant(@_f.num_vars))]
    #[maintains((mut self).equisat_extension(*_f))]
    #[ensures((@self).len() == (@(^self)).len())]
    pub fn swap_lits_in_clause(&mut self, _f: &Formula, j: usize, k: usize) {
        let old_c = ghost! { self };
        self.rest.swap(j, k);
        proof_assert!(^old_c.inner() == ^self);
        proof_assert!((*old_c.inner()).equisat_extension(*_f));
        proof_assert!(self.invariant(@_f.num_vars));
        proof_assert!((@self).exchange(@old_c.inner(), @j, @k));
        proof_assert!((@old_c.inner()).permut(@self, 0, (@self).len()));
        proof_assert!(self.equisat(*old_c.inner()));
        proof_assert!(self.equisat2(*old_c.inner(), *_f));
        proof_assert!(^old_c.inner() == ^self);
        // This is the critical assertion. TODO: Look at the assertions above and remove the unneded ones.
        proof_assert!(eventually_sat_complete_no_ass((((@_f).0).push(*self), (@_f).1)) ==
                      eventually_sat_complete_no_ass((((@_f).0).push(*old_c.inner()), (@_f).1)));
        proof_assert!(self.equisat_extension(*_f));
    }

    #[cfg_attr(feature = "trust_clause", trusted)]
    #[requires((@t.lit_to_level).len() == (@_f.num_vars))]
    #[requires(self.invariant(@_f.num_vars))]
    pub fn calc_lbd(&self, _f: &Formula, s: &mut Solver, t: &Trail) -> usize {
        let mut i: usize = 0;
        let mut lbd: usize = 0;
        #[invariant(lbd_bound, @lbd <= @i)]
        while i < self.len() {
            let level = t.lit_to_level[self.rest[i].index()];
            if level < s.perm_diff.len() && // Lazy
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
