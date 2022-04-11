extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::{
    clause::*,
    decision::*,
    formula::*,
    lit::*,
    trail::*,
};

#[cfg(contracts)]
use crate::logic::{
    logic::*,
    logic_assignments::*,
    logic_clause::*,
    logic_trail::*,//{trail_invariant, long_are_post_unit_inner_new},
};

pub type AssignedState = u8;
// A.1 is temporary
pub struct Assignments(pub Vec<AssignedState>, pub usize);


#[trusted]
#[ensures(@l <= @result && @result  < @u)]
fn rand_in_range(l: usize, u: usize) -> u8 {
    use creusot_contracts::rand::Rng;
    let n = rand::thread_rng().gen_range(l..u);
    n as u8
}

impl Assignments {
    // Ok
    #[inline(always)]
    #[cfg_attr(all(any(trust_assignments, trust_all), not(untrust_all)), trusted)]
    #[ensures(@result === (@self).len())]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    // OK
    #[inline(always)]
    #[cfg_attr(all(any(trust_assignments, trust_all), not(untrust_all)), trusted)]
    #[maintains((mut self).invariant(*_f))]
    #[requires(lit.invariant(@_f.num_vars))]
    #[requires(_f.invariant())]
    #[requires(trail_invariant(@_t, *_f))] 
    #[requires(unset((@self)[@lit.idx]))] // Added, will break stuff further up
    #[requires(long_are_post_unit_inner(@_t, *_f, @self))]
    #[ensures(@(@^self)[@lit.idx] === 1 || @(@^self)[@lit.idx] === 0)]
    #[ensures((@^self).len() === (@self).len())]
    #[ensures(long_are_post_unit_inner(@_t, *_f, @^self))]
    #[ensures((forall<j : Int> 0 <= j && j < (@self).len() &&
        j != @lit.idx ==> (@*self)[j] === (@^self)[j]))]
    #[ensures(lit.sat(^self))]
    pub fn set_assignment(&mut self, lit: Lit, _f: &Formula, _t: &Vec<Step>) {
        let old_self = Ghost::record(&self);
        proof_assert!((lemma_assign_maintains_long_are_post_unit(@_t, *_f, *self, lit));true);
        // zzTODOzz 
        //self.0[lit.idx] = lit.polarity as u8;
        if lit.polarity {
            self.0[lit.idx] = 1;
            proof_assert!(@self == (@@old_self).set(@lit.idx, 1u8));
        } else {
            self.0[lit.idx] = 0;
            proof_assert!(@self == (@@old_self).set(@lit.idx, 0u8));
        }
        proof_assert!((lemma_assign_maintains_long_are_post_unit(@_t, *_f, *@old_self, lit));true);
        proof_assert!(^@old_self === ^self);
        proof_assert!(long_are_post_unit_inner(@_t, *_f, @self));
    }

    // OK
    #[cfg_attr(all(any(trust_assignments, trust_all), not(untrust_all)), trusted)]
    #[requires(f.invariant())]
    #[ensures(result.invariant(*f))]
    pub fn new(f: &Formula) -> Self {
        let mut assign: Vec<AssignedState> = Vec::new();
        let mut i: usize = 0;
        #[invariant(loop_invariant, 0 <= @i && @i <= @f.num_vars)]
        #[invariant(length_invariant, (@assign).len() === @i)]
        #[invariant(all_less, forall<j: Int> 0 <= j && j < @i ==> @(@assign)[j] <= 3)]
        while i < f.num_vars {
            // Having it random didnt really help
            let n = rand_in_range(2,4);
            assign.push(n);
            i += 1
        }
        Assignments(assign, 0)
    }

    // OK
    #[cfg_attr(all(any(trust_assignments, trust_all), not(untrust_all)), trusted)]
    #[maintains((mut self).invariant(*_f))]
    #[requires(d.invariant((@self).len()))]
    #[ensures(match result {
        Some(res) => @res < (@self).len() && unset((@self)[@res]),
        None => self.complete(),
    })]
    #[ensures(@self === @^self)]
    pub fn find_unassigned(&mut self, d: &Decisions, _f: &Formula) -> Option<usize> {
        let mut i: usize = self.1;
        #[invariant(i_bound, @i <= (@d.lit_order).len())]
        while i < d.lit_order.len() {
            let curr = self.0[d.lit_order[i]];
            if curr >= 2 {
                //let b = curr != 2;
                self.1 = i + 1;
                //return Some(Lit{ idx: d.lit_order[i], polarity: b });
                return Some(d.lit_order[i]);
            }
            i += 1;
        }
        // Strictly speaking this is an unecessary runtime check, but it only gets run at most once and it
        // greatly simplifies the proof.
        i = 0;
        #[invariant(prev, forall<j: Int> 0 <= j && j < @i ==> !unset((@self)[j]))]
        while i < self.0.len() {
            if self.0[i] >= 2 {
                return Some(i);
            }
            i += 1;
        }
        None
    }
}