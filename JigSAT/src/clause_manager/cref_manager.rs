use std::ops::{Index, IndexMut};

use crate::clause_manager::{common::CRef};

pub struct CRefManager {
    pub(crate) crefs: Vec<CRef>,
}

impl Index<usize> for CRefManager {
    type Output = CRef;
    #[inline]
    fn index(&self, i: usize) -> &Self::Output {
        #[cfg(not(feature = "safe_access"))]
        unsafe { self.crefs.get_unchecked(i) }
        #[cfg(feature = "safe_access")]
        &self.crefs[i]
    }
}
impl IndexMut<usize> for CRefManager {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        #[cfg(not(feature = "safe_access"))]
        unsafe { self.crefs.get_unchecked_mut(i) }
        #[cfg(feature = "safe_access")]
        &mut self.crefs[i]
    }
}

impl CRefManager {
    pub(crate) fn new() -> Self {
        Self {
            crefs: Vec::new(),
        }
    }

    pub(crate) fn add_cref(&mut self, cref: CRef) {
        self.crefs.push(cref);
    }

    pub(crate) fn len(&self) -> usize {
        self.crefs.len()
    }
}