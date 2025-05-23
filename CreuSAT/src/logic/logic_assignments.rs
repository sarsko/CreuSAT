use creusot_contracts::{model::*, std::*, *};

use crate::{
    assignments::*,
    decision::*,
    formula::*,
    trail::{Step, Trail},
};

use crate::logic::{logic::*, logic_formula::*};

#[cfg(creusot)]
impl View for Assignments {
    type ViewTy = Seq<AssignedState>;

    #[logic]
    #[open]
    fn view(self) -> Self::ViewTy {
        self.0.view()
    }
}

#[predicate]
#[open]
pub fn compatible_inner(a: Seq<AssignedState>, a2: Seq<AssignedState>) -> bool {
    pearlite! {
        a.len() == a2.len() && (forall<i: Int> 0 <= i && i < a.len() ==>
            (unset(a[i]) || a[i] == a2[i]))
    }
}

#[predicate]
#[open]
pub fn complete_inner(a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < a.len() ==> !unset(a[i])
    }
}

#[predicate]
#[open]
pub fn compatible_complete_inner(a: Seq<AssignedState>, a2: Seq<AssignedState>) -> bool {
    compatible_inner(a, a2) && complete_inner(a2)
}

// Predicates
impl Assignments {
    #[predicate]
    #[open]
    pub fn inv(self, f: Formula) -> bool {
        pearlite! {
            f.num_vars@ == self@.len()
            && forall<i: Int> 0 <= i && i < self@.len() ==> self@[i]@ <= 3
        }
    }

    #[predicate]
    #[open]
    pub fn complete(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self@.len() ==> !unset(self@[i])
        }
    }
}
