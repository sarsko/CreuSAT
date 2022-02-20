extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::lit::*;
use crate::assignments::*;

use crate::formula::*;
//#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Clause(pub Vec<Lit>);

impl Model for Clause {
    type ModelTy = Seq<Lit>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        self.0.model()
    }
}

impl Clause {
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
            forall<j: Int, k: Int> 0 <= j && j < (@self).len() ==>
                 0 <= k && k < (@self).len() ==> j != k ==> !(@((@self)[k]).idx === @((@self)[j]).idx)
        }
    }

    #[predicate]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! { self.vars_in_range(@f.num_vars) && self.no_duplicate_indexes() && (@self).len() > 0 }
    }
}

impl Clause {
    #[requires(a.invariant(@_f.num_vars))]
    #[requires(self.invariant(*_f))]
    pub fn is_unsat(&self, a: &Assignments, _f: &Formula) -> bool {
        let mut i = 0;
        while i < self.0.len() {
            let lit = self.0[i];
            let res = a.0[lit.idx];
            match res {
                Some(x) => {
                    // false, false || true, true -> clause is SAT
                    if lit.polarity == x {
                        return false;
                    }
                }
                None => {
                    return false;
                } // May become SAT
            }
            i += 1;
        }
        return true;
    }
}