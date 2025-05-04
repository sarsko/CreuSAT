
use creusot_contracts::{std::*, *};

use crate::{formula::*, lit::*, trail::*};
use ::std::ops::{Index, IndexMut};

#[allow(unused_features)]
#[cfg(creusot)]
use crate::logic::{logic::*, logic_assignments::*, logic_clause::*, logic_trail::*};

pub type AssignedState = u8;

// TODO: Remove pub
pub struct Assignments(pub Vec<AssignedState>);

impl Index<usize> for Assignments {
    type Output = AssignedState;
    #[inline]
    #[cfg_attr(feature = "trust_assignments", trusted)]
    #[requires(ix@ < self@.len())]
    #[ensures(self@[ix@] == *result)]
    fn index(&self, ix: usize) -> &AssignedState {
        #[cfg(not(creusot))]
        unsafe {
            self.0.get_unchecked(ix)
        }
        #[cfg(creusot)]
        &self.0[ix]
    }
}

impl IndexMut<usize> for Assignments {
    #[inline]
    #[cfg_attr(feature = "trust_assignments", trusted)]
    #[requires(ix@ < self@.len())]
    #[ensures((*self)@[ix@] == *result)]
    #[ensures((^self)@[ix@] == ^result)]
    #[ensures(forall<i: Int> 0 <= i && i != ix@ && i < self@.len() ==> self@[i] == (^self)@[i])]
    #[ensures((^self)@.len() == (*self)@.len())]
    fn index_mut(&mut self, ix: usize) -> &mut AssignedState {
        #[cfg(not(creusot))]
        unsafe {
            self.0.get_unchecked_mut(ix)
        }
        #[cfg(creusot)]
        &mut self.0[ix]
    }
}

impl Assignments {
    // Ok
    #[inline(always)]
    #[cfg_attr(feature = "trust_assignments", trusted)]
    #[ensures(result@ == self@.len())]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[inline(always)]
    #[cfg_attr(feature = "trust_assignments", trusted)]
    #[maintains((mut self).inv(*_f))]
    #[requires(lit.inv(_f.num_vars@))]
    #[requires(_f.inv())]
    #[requires(trail_invariant(_t@, *_f))]
    #[requires(unset(self@[lit.index_logic()]))]
    #[requires(long_are_post_unit_inner(_t@, *_f, self@))]
    #[ensures(long_are_post_unit_inner(_t@, *_f, (^self)@))]
    #[ensures(!unset((^self)@[lit.index_logic()]))]
    #[ensures((^self)@.len() == self@.len())]
    #[ensures((forall<j: Int> 0 <= j && j < self@.len() && j != lit.index_logic() ==> self@[j] == (^self)@[j]))]
    #[ensures(lit.sat(^self))]
    pub fn set_assignment(&mut self, lit: Lit, _f: &Formula, _t: &Vec<Step>) {
        let old_self: Snapshot<&mut Assignments> = snapshot! { self };
        //self.clauses[lit.index()] = lit.is_positive() as u8;
        if lit.is_positive() {
            self.0[lit.index()] = 1;
        } else {
            self.0[lit.index()] = 0;
        }
    }

    // OK
    #[cfg_attr(feature = "trust_assignments", trusted)]
    #[requires(f.inv())]
    #[ensures(result.inv(*f))]
    pub fn new(f: &Formula) -> Self {
        Assignments(vec::from_elem(2, f.num_vars))
    }
}
