extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

pub(crate) type AssignedState = u8;

#[logic]
fn pos() -> AssignedState {
    1u8
}

#[logic]
fn neg() -> AssignedState {
    0u8
}

#[predicate]
pub fn unset(v: AssignedState) -> bool {
    pearlite! {
        if @v >= 2 {
            true
        } else {
            false
        }
    }
}

#[logic]
//#[ensures(b ==> @result == 1)]
//#[ensures(!b ==> @result == 0)]
pub fn bool_to_assignedstate(b: bool) -> AssignedState {
    if b {
        1u8
    } else {
        0u8
    }
}

// Mapping from index to assignment
#[cfg(feature = "contracts")]
pub struct AssignmentsLogic(Seq<AssignedState>);

#[cfg(feature = "contracts")]
pub struct LitLogic {
    pub idx: Int,
    pub polarity: bool,
}

use crate::solver::Lit;
#[cfg(feature = "contracts")]
pub struct ClauseLogic {
    pub lits: Set<Lit>,
}

use crate::solver::Clause;
#[cfg(feature = "contracts")]
pub struct FormulaLogic(pub Set<Clause>);

#[cfg(feature = "contracts")]
impl LitLogic {
    #[predicate]
    pub(crate) fn sat(self, m: AssignmentsLogic) -> bool {
        m.0[self.idx] == bool_to_assignedstate(self.polarity)
    }

    #[predicate]
    pub(crate) fn idx_less_than(self, upper_bound: Int) -> bool {
        0 <= self.idx && self.idx < upper_bound
    }
}

#[cfg(feature = "contracts")]
impl ClauseLogic {
    #[predicate]
    pub(crate) fn idxes_less_than(self, upper_bound: Int) -> bool {
        pearlite! { forall<l: _> self.lits.contains(l) ==> (@l).idx_less_than(upper_bound) }
    }

    #[predicate]
    pub(crate) fn sat(self, m: AssignmentsLogic) -> bool {
        pearlite! { exists<l: _> self.lits.contains(l) && (@l).sat(m) }
    }
}

#[cfg(feature = "contracts")]
impl FormulaLogic {
    #[predicate]
    pub(crate) fn idxes_less_than(self, upper_bound: Int) -> bool {
        pearlite! { forall<c: _> self.0.contains(c) ==> (@c).idxes_less_than(upper_bound) }
    }

    #[predicate]
    pub(crate) fn sat(self, m: AssignmentsLogic) -> bool {
        pearlite! { forall<c: _> self.0.contains(c) ==> (@c).sat(m) }
    }
}
