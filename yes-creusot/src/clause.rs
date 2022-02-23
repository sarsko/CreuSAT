extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::lit::*;
use crate::assignments::*;

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
            forall<i: Int> 0 <= i && i < (@self).len() ==>
                (0 <= @((@self)[i]).idx && @((@self)[i]).idx < n)
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
    #[trusted] // Todo look at
    #[inline]
    pub fn clause_from_vec(vec: &Vec<Lit>) -> Clause {
        let mut rest_vec = Vec::new();
        let mut i = 2;
        while i < vec.len() {
            rest_vec.push(vec[i]);
            i += 1;
        }
        Clause {
            first: vec[0],
            second: vec[1],
            rest: rest_vec,
        }
    }
}