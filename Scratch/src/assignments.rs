use creusot_contracts::std::*;
use creusot_contracts::*;

#[cfg(creusot)]
use crate::logic::*;

use crate::formula::*;

// ===== Assignments =====
pub type AssignedState = u8;

pub struct Assignments(pub Vec<AssignedState>);

#[cfg(creusot)]
impl View for Assignments {
    type ViewTy = Seq<AssignedState>;

    #[open]
    #[logic]
    fn view(self) -> Self::ViewTy {
        self.0.view()
    }
}

#[open]
#[predicate]
pub fn compatible_inner(a: Seq<AssignedState>, a2: Seq<AssignedState>) -> bool {
    pearlite! {
        a.len() == a2.len() && (forall<i: Int> 0 <= i && i < a.len() ==>
            (unset(a[i]) || a[i] == a2[i]))
    }
}

#[open]
#[predicate]
pub fn complete_inner(a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < a.len() ==> !unset(a[i])
    }
}

#[open]
#[predicate]
pub fn compatible_complete_inner(a: Seq<AssignedState>, a2: Seq<AssignedState>) -> bool {
    compatible_inner(a, a2) && complete_inner(a2)
}

// Predicates
impl Assignments {
    #[open]
    #[predicate]
    pub fn inv(self, f: Formula) -> bool {
        pearlite! {
            f.num_vars@ == self@.len()
            && forall<i: Int> 0 <= i && i < self@.len() ==> self@[i]@ <= 3
        }
    }

    #[open]
    #[predicate]
    pub fn complete(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self@.len() ==> !unset(self@[i])
        }
    }
}
