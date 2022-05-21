extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{clause::*, decision::*, formula::*, lit::*, trail::*};

use crate::util::*;

#[allow(unused_features)]
#[cfg(feature = "contracts")]
use crate::logic::{
    logic::*,
    logic_assignments::*,
    logic_clause::*,
    logic_trail::*, //{trail_invariant, long_are_post_unit_inner_new},
};

pub type AssignedState = u8;
// A.1 is temporary
pub struct Assignments(pub Vec<AssignedState>);

#[cfg_attr(not(untrust_perm), trusted)]
#[ensures(@l <= @result && @result  < @u)]
fn rand_in_range(l: usize, u: usize) -> u8 {
    use creusot_contracts::rand::Rng;
    let n = rand::thread_rng().gen_range(l..u);
    n as u8
}

impl Assignments {
    // Ok
    #[inline(always)]
    #[cfg_attr(feature = "trust_assignments", trusted)]
    #[ensures(@result == (@self).len())]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    // OK
    #[inline(always)]
    #[cfg_attr(feature = "trust_assignments", trusted)]
    #[maintains((mut self).invariant(*_f))]
    #[requires(lit.invariant(@_f.num_vars))]
    #[requires(_f.invariant())]
    #[requires(trail_invariant(@_t, *_f))]
    #[requires(unset((@self)[lit.index_logic()]))]
    #[requires(long_are_post_unit_inner(@_t, *_f, @self))]
    #[ensures(long_are_post_unit_inner(@_t, *_f, @^self))]
    #[ensures(!unset((@^self)[lit.index_logic()]))]
    #[ensures((@^self).len() == (@self).len())]
    #[ensures((forall<j : Int> 0 <= j && j < (@self).len() 
            && j != lit.index_logic() ==> (@*self)[j] == (@^self)[j]))]
    #[ensures(lit.sat(^self))]
    pub fn set_assignment(&mut self, lit: Lit, _f: &Formula, _t: &Vec<Step>) {
        let old_self = Ghost::record(&self);
        //self.0[lit.index()] = lit.is_positive() as u8;
        proof_assert!((lemma_assign_maintains_long_are_post_unit(@_t, *_f, *@old_self, lit)); true);
        if lit.is_positive() {
            self.0[lit.index()] = 1;
        } else {
            self.0[lit.index()] = 0;
        }
        proof_assert!((lemma_assign_maintains_long_are_post_unit(@_t, *_f, *@old_self, lit)); true);
        proof_assert!(^@old_self == ^self);
        proof_assert!(long_are_post_unit_inner(@_t, *_f, @self));
    }

    // OK
    #[cfg_attr(feature = "trust_assignments", trusted)]
    #[requires(f.invariant())]
    #[ensures(result.invariant(*f))]
    pub fn new(f: &Formula) -> Self {
        Assignments(vec::from_elem(2, f.num_vars))
    }
}
