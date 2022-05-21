extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{assignments::*, formula::*, lit::*};

#[cfg(feature = "contracts")]
use crate::logic::logic_clause::*;

pub struct Clause {
    pub deleted: bool,
    pub rest: Vec<Lit>,
}

// Split up invariant and at least binary and revert to
// old invariant instead of invariant_unary_ok

impl Clone for Clause {
    // Will do last
    #[trusted] // TODO
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        Clause { deleted: self.deleted, rest: self.rest.clone() }
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
        return false;
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
        return true;
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
    pub fn clause_from_vec(vec: &Vec<Lit>) -> Clause {
        Clause { deleted: false, rest: vec.clone() }
    }

    #[inline(always)]
    #[cfg_attr(feature = "trust_clause", trusted)]
    #[maintains((mut self).invariant_unary_ok(@_f.num_vars))]
    #[requires((@self).len() > 0)]
    #[requires(@idx < (@self).len())]
    #[ensures(forall<i: Int> 0 <= i && i < (@(^self)).len() ==>
        (exists<j: Int> 0 <= j && j < (@self).len() && (@(^self))[i] == (@self)[j]))]
    #[ensures(forall<i: Int> 0 <= i && i < (@(self)).len() ==>
        (exists<j: Int> 0 <= j && j < (@(^self)).len() && (@(^self))[i] == (@self)[j]))]
    #[ensures((@(^self)).len() == (@self).len())]
    fn move_to_end(&mut self, idx: usize, _f: &Formula) {
        let old_self = Ghost::record(&self);
        let end = self.rest.len() - 1;
        self.rest.swap(idx, end);
        proof_assert!(^@old_self == ^self);
    }

    #[inline(always)]
    #[cfg_attr(feature = "trust_clause", trusted)]
    #[maintains((mut self).invariant_unary_ok(@_f.num_vars))]
    #[requires((@self).len() > 0)]
    #[requires(@idx < (@self).len())]
    #[ensures(forall<i: Int> 0 <= i && i < (@(^self)).len() ==>
        exists<j: Int> 0 <= j && j < (@self).len() && (@(^self))[i] == (@self)[j])]
    #[ensures((@(^self)).len() + 1 == (@self).len())]
    pub fn remove_from_clause(&mut self, idx: usize, _f: &Formula) {
        self.move_to_end(idx, _f);
        self.rest.pop();
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
        return self.rest[0].lit_unset(a);
    }
}
