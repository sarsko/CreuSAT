extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{
    assignments::*,
    decision::*,
    formula::*,
    trail::{Step, Trail},
};

use crate::logic::{logic::*, logic_formula::*};

#[cfg(feature = "contracts")]
impl Model for Assignments {
    type ModelTy = Seq<AssignedState>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        self.0.model()
    }
}

#[predicate]
pub fn assignments_equality(a: Assignments, a2: Assignments) -> bool {
    pearlite! {
        (@a).len() === (@a2).len() &&
            forall<i: Int> 0 <= i && i < (@a).len() ==> (@a)[i] === (@a2)[i]
    }
}

#[predicate]
pub fn compatible_inner(a: Seq<AssignedState>, a2: Seq<AssignedState>) -> bool {
    pearlite! {
        a.len() === a2.len() && (forall<i: Int> 0 <= i && i < a.len() ==>
            (unset(a[i]) || a[i] === a2[i]))
    }
}

#[predicate]
pub fn complete_inner(a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < a.len() ==> !unset(a[i])
    }
}

#[predicate]
pub fn compatible_complete_inner(a: Seq<AssignedState>, a2: Seq<AssignedState>) -> bool {
    pearlite! {
        compatible_inner(a, a2) && complete_inner(a2)
    }
}

#[predicate]
pub fn assignments_invariant(a: Seq<AssignedState>, f: Formula) -> bool {
    pearlite! {
        @f.num_vars === a.len()
        && forall<i : Int> 0 <= i && i < a.len() ==> @a[i] <= 3 // NEW, may break stuff
    }
}

// Predicates
impl Assignments {
    #[predicate]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            @f.num_vars === (@self).len()
            //&& @self.1 <= @f.num_vars // We dont have self.1(search index) anymore
            && forall<i : Int> 0 <= i && i < (@self).len() ==> @(@self)[i] <= 3 // NEW, may break stuff
        }
    }

    // I believe all of these can be removed ?
    #[predicate]
    pub fn compatible(self, a2: Assignments) -> bool {
        pearlite! { compatible_inner(@self, @a2) }
    }

    #[predicate]
    pub fn complete(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self).len() ==> !unset((@self)[i])
        }
    }

    #[predicate]
    pub fn compatible_complete(self, a2: Assignments) -> bool {
        self.compatible(a2) && a2.complete()
    }
}
