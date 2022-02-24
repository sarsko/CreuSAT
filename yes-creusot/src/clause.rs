extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::lit::*;
//use crate::assignments::*;

use crate::formula::*;
//#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Clause{
    pub first: Lit,
    pub second: Lit,
    pub rest: Vec<Lit>,
}

// Remove this
impl Model for Clause {
    type ModelTy = Seq<Lit>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        self.rest.model()
    }
}

#[logic]
#[requires(c.vars_in_range(n))]
#[ensures(c.idxs_in_range(2*n))]
pub fn lemma_vars_in_range_implies_watchidx_in_range(c: Clause, n: Int) {}

#[predicate]
pub fn no_duplicate_indexes(c: Seq<Lit>) -> bool {
    pearlite! {
        forall<j: Int, k: Int> 0 <= j && j < (c).len() ==>
                0 <= k && k < (c).len() ==> j != k ==> !(@((c)[k]).idx === @((c)[j]).idx) 
    }
}

#[predicate]
pub fn vars_in_range(c: Seq<Lit>, n: Int) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < (c).len() ==>
            (0 <= @((c)[i]).idx && @((c)[i]).idx < n)
    }
}

#[predicate]
pub fn invariant(c: Seq<Lit>, f: Formula) -> bool {
    pearlite! { vars_in_range(c, @f.num_vars) &&  no_duplicate_indexes(c) }
}

impl Clause {
    #[predicate]
    pub fn first_two_ok(self, n: Int) -> bool {
        pearlite! {
            0 <= @self.first.idx && @self.first.idx < n && 0 <= @self.second.idx && @self.second.idx < n
        }
    }

    #[predicate]
    pub fn vars_in_range(self, n: Int) -> bool {
        pearlite! {
            (0 <= @self.first.idx && @self.first.idx < n) &&
            (0 <= @self.second.idx && @self.second.idx < n) &&
            forall<i: Int> 0 <= i && i < (@self).len() ==>
                (0 <= @((@self)[i]).idx && @((@self)[i]).idx < n)
        }
    }
    
    #[predicate]
    pub fn idxs_in_range(self, n: Int) -> bool {
        pearlite! {
            (0 <= self.first.to_neg_watchidx_logic() && self.first.to_neg_watchidx_logic() < n) &&
            (0 <= self.second.to_neg_watchidx_logic() && self.second.to_neg_watchidx_logic() < n) &&
            forall<i: Int> 0 <= i && i < (@self).len() ==>
                (0 <= ((@self)[i]).to_neg_watchidx_logic() && ((@self)[i]).to_neg_watchidx_logic() < n)
        }
    }

    // Swapped the implementation to the one for distinct from why3 stdlib. Might require reinit
    // Ok I was lacking 0 <= k might not need reinit after all
    #[predicate]
    pub fn no_duplicate_indexes(self) -> bool {
        pearlite! {
            /*
            forall<j: Int, k: Int> 0 <= j && j < (@self).len() &&
                 0 <= k && k < j ==> !(@(@self)[k].idx === @(@self)[j].idx)
                 */
            !(@self.first.idx === @self.second.idx) &&
            forall<j: Int, k: Int> 0 <= j && j < (@self).len() ==>
                 0 <= k && k < (@self).len() ==> j != k ==> !(@((@self)[k]).idx === @((@self)[j]).idx) && 
                 !(@((@self)[j]).idx === @self.first.idx) &&
                 !(@((@self)[j]).idx === @self.second.idx)
        }
    }

    #[predicate]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! { self.first_two_ok(@f.num_vars) && self.vars_in_range(@f.num_vars) && self.no_duplicate_indexes() }
    }
}

impl Clause {
    #[trusted] // OK
    //#[inline]
    #[requires((@vec).len() >= 2)]          
    #[requires(forall<i: Int> 0 <= i && i < (@vec).len() ==> @(@vec)[i].idx < @_f.num_vars)]
    #[requires(no_duplicate_indexes(@vec))]
    #[ensures(result.second === (@vec)[1])]
    #[ensures(result.second === (@vec)[1])]
    #[ensures(result.invariant(*_f))]
    pub fn clause_from_vec(vec: &Vec<Lit>, _f: &Formula) -> Clause {
        let mut rest_vec: Vec<Lit> = Vec::new();
        let mut i : usize = 2;
        #[invariant(i_less, 2 <= @i && @i <= (@vec).len())]
        #[invariant(rest_vec_len, (@rest_vec).len() === @i - 2)]
        #[invariant(same_elems, forall<j: Int> 0 <= j && j < (@rest_vec).len() ==> (@rest_vec)[j] === (@vec)[j + 2])]
        while i < vec.len() {
            rest_vec.push(vec[i]);
            i += 1;
        }
        let clause = Clause {
            first: vec[0],
            second: vec[1],
            rest: rest_vec,
        };
        proof_assert!(clause.first === (@vec)[0]);
        proof_assert!(clause.second === (@vec)[1]);
        clause
    }
}