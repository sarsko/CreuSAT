use crate::{formula::*, lit::*, trail::*};
use std::ops::{Index, IndexMut};

pub type AssignedState = u8;
pub struct Assignments(pub Vec<AssignedState>);

impl Index<usize> for Assignments {
    type Output = AssignedState;
    #[inline]
    fn index(&self, i: usize) -> &AssignedState {
        //#[cfg(feature = "unsafe_access")]
        unsafe { self.0.get_unchecked(i) }
        //#[cfg(not(feature = "unsafe_access"))]
        //&self.lits[i]
    }
}

impl IndexMut<usize> for Assignments {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut AssignedState {
        //#[cfg(feature = "unsafe_access")]
        unsafe { self.0.get_unchecked_mut(i) }
        //#[cfg(not(feature = "unsafe_access"))]
        //&mut self.lits[i]
    }
}

impl Assignments {
    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub fn set_assignment(&mut self, lit: Lit, _f: &Formula, _t: &[Step]) {
        self[lit.index()] = lit.is_positive() as u8;
    }

    #[inline]
    pub fn new(f: &Formula) -> Self {
        Assignments(vec![2; f.num_vars])
    }

    #[inline]
    pub(crate) fn is_assigned(&self, idx: usize) -> bool {
        self[idx] < 2
    }
}
