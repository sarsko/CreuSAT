extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::{
    assignments::*,
    formula::*,
    lit::*,
};

#[cfg(contracts)]
use crate::logic::{
    logic_clause::*
};

//#[cfg_attr(not(contracts), derive(Debug))]
#[derive(Debug)]
//#[derive(Clone)]
pub struct Clause {
    pub deleted: bool,
    //pub first: Lit,
    //pub second: Lit,
    pub rest: Vec<Lit>
}

// Split up invariant and at least binary and revert to
// old invariant instead of invariant_unary_ok

impl Clone for Clause {
    // Will do last
    #[trusted] // TODO
    #[ensures(result === *self)]
    fn clone(&self) -> Self {
        Clause {
            deleted: self.deleted,
            rest: self.rest.clone()
        }
    }
}

//#[derive(Copy, Clone, Eq)]
pub enum ClauseState {
    Sat,
    Unsat,
    Unit,
    Unknown,
    Err(usize),
}

impl Clause {
    #[cfg_attr(all(any(trust_clause, trust_all), not(untrust_all)), trusted)]
    #[ensures(result === self.invariant(@n))]
    pub fn check_clause_invariant(&self, n: usize) -> bool {
        let mut i: usize = 0;
        #[invariant(inv, forall<j: Int> 0 <= j && j < @i ==> (@self)[j].invariant(@n))]
        while i < self.len() {
            if !self.rest[i].check_lit_invariant(n){
                return false;
            }
            i += 1;
        }
        if self.no_duplicates() {
            return true;
        }
        return false;
    }


    #[cfg_attr(all(any(trust_clause, trust_all), not(untrust_all)), trusted)]
    #[ensures(result === self.no_duplicate_indexes())]
    pub fn no_duplicates(&self) -> bool {
        let mut i: usize = 0;
        #[invariant(no_dups, 
            forall<j: Int, k: Int> 0 <= j && j < @i &&
             0 <= k && k < j ==> (@self)[j].idx != (@self)[k].idx)]
        while i < self.rest.len() {
            let lit1 = self.rest[i];
            let mut j: usize = 0;
            #[invariant(inv, forall<k: Int> 0 <= k && k < @j ==> lit1.idx != (@self)[k].idx)]
            while j < i {
                let lit2 = self.rest[j];
                if lit1.idx == lit2.idx {
                    return false;
                }
                j += 1;
            }
            i += 1;
        }
        return true;
    }

    #[inline(always)]
    #[cfg_attr(all(any(trust_assignments, trust_all), not(untrust_all)), trusted)]
    #[ensures(@result === (@self).len())]
    pub fn len(&self) -> usize {
        self.rest.len()
    }
    
    /*
    #[cfg_attr(all(any(trust_clause, trust_all), not(untrust_all)), trusted)]
    pub fn make_unit_clause(lit: Lit) -> Clause {
        Clause{ rest: vec::from_elem(lit, 1) }
    }
    */

    // TODO
    // Better to just fix the parser. Gotta have a decent parser by delivery anyways
    #[inline]
    #[trusted] 
    //#[ensures(result.invariant(@_f.num_vars))]
    //#[ensures((@result).len() >= 2)]
    pub fn clause_from_vec(vec: &std::vec::Vec<Lit>) -> Clause {
        Clause { 
            deleted: false,
            rest: vec.clone() 
        }
        /*
        Clause {
            first: vec[0],
            second: vec[1],
            rest: vec[2..].to_vec()
        }
        */
    }

    // OK with split + split + CVC4 for 4.49 seconds on Mac 
    #[inline(always)]
    #[cfg_attr(all(any(trust_clause, trust_all), not(untrust_all)), trusted)]
    #[maintains((mut self).invariant_unary_ok(@_f.num_vars))]
    #[requires((@self).len() > 0)]
    #[requires(@idx < (@self.rest).len())]
    #[ensures(forall<i: Int> 0 <= i && i < (@(^self).rest).len() ==> 
        exists<j: Int> 0 <= j && j < (@self.rest).len() && (@(^self))[i] === (@self)[j])]
    #[ensures(forall<i: Int> 0 <= i && i < (@(self).rest).len() ==> 
        exists<j: Int> 0 <= j && j < (@(^self).rest).len() && (@(^self))[i] === (@self)[j])]
    #[ensures((@(^self).rest).len() === (@self.rest).len())]
    fn move_to_end(&mut self, idx: usize, _f: &Formula) {
        let old_self = Ghost::record(&self);
        let end = self.rest.len() - 1;
        self.rest.swap(idx, end);
        proof_assert!(^@old_self === ^self);
        /*
        proof_assert!((@self).permutation_of(@@old_self));
        proof_assert!(forall<i: Int> 0 <= i && i < (@(self).rest).len() ==> 
            exists<j: Int> 0 <= j && j < (@(@old_self).rest).len() && (@(self))[i] === (@(@old_self))[j]);
        proof_assert!(forall<i: Int> 0 <= i && i < (@(@old_self).rest).len() ==> 
            exists<j: Int> 0 <= j && j < (@self.rest).len() && (@(self))[i] === (@(@old_self))[j]);
        proof_assert!((@(@old_self).rest).len() === (@self.rest).len());
        */
    }

    // They check out on Linux
    #[inline(always)]
    #[cfg_attr(all(any(trust_clause, trust_all), not(untrust_all)), trusted)]
    #[maintains((mut self).invariant_unary_ok(@_f.num_vars))]
    #[requires((@self).len() > 0)]
    #[requires(@idx < (@self.rest).len())]
    #[ensures(forall<i: Int> 0 <= i && i < (@(^self).rest).len() ==> 
    exists<j: Int> 0 <= j && j < (@self.rest).len() && (@(^self))[i] === (@self)[j])]
    #[ensures((@(^self).rest).len() + 1 === (@self.rest).len())]
    pub fn remove_from_clause(&mut self, idx: usize, _f: &Formula) {
        self.move_to_end(idx, _f);
        self.rest.pop();
    }
}