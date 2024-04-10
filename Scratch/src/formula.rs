extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{assignments::*, clause::*, lit::*};

// ===== Formula =====
pub struct Formula {
    pub clauses: Vec<Clause>,
    pub num_vars: usize,
}

#[cfg(creusot)]
impl ShallowModel for Formula {
    type ShallowModelTy = (Seq<Clause>, Int);

    #[open]
    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        (self.clauses.shallow_model(), self.num_vars.shallow_model())
    }
}

#[open]
#[predicate]
pub fn formula_invariant(f: (Seq<Clause>, Int)) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < f.0.len() ==>
            (f.0[i].invariant(f.1) && f.0[i]@.len() > 0)
    }
}

#[open]
#[predicate]
pub fn formula_sat_inner(f: (Seq<Clause>, Int), a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < f.0.len() ==>
            f.0[i].sat_inner(a)
    }
}

#[open]
#[predicate]
pub fn eventually_sat_complete(f: (Seq<Clause>, Int)) -> bool {
    pearlite! {
        exists<a2: Seq<AssignedState>> a2.len() == f.1 && complete_inner(a2) && formula_sat_inner(f, a2)
    }
}

#[open]
#[predicate]
fn equisat(f: (Seq<Clause>, Int), o: (Seq<Clause>, Int)) -> bool {
    pearlite! {
        eventually_sat_complete(f) == eventually_sat_complete(o)
    }
}

// Predicates
impl Formula {
    #[open]
    #[predicate]
    pub fn eventually_sat_complete(self) -> bool {
        pearlite! {
            exists<a2: Seq<AssignedState>> a2.len() == self.num_vars@ && complete_inner(a2) && self.sat_inner(a2)
        }
    }

    #[open]
    #[predicate]
    pub fn equisat(self, o: Formula) -> bool {
        self.eventually_sat_complete() == o.eventually_sat_complete()
    }

    #[open]
    #[predicate]
    #[cfg_attr(feature = "trust_formula_logic", trusted)]
    #[ensures(result == self.invariant_mirror())] // Removing this makes a bunch of seemingly unrelated things fail
    pub fn invariant(self) -> bool {
        pearlite! { formula_invariant(self@) }
    }

    #[open]
    #[predicate]
    fn invariant_mirror(self) -> bool {
        pearlite! {
            (forall<i: Int> 0 <= i && i < self.clauses@.len() ==>
                self.clauses@[i].invariant(self.num_vars@))
            &&
            (forall<i: Int> 0 <= i && i < self.clauses@.len() ==>
                self.clauses@[i]@.len() >= 1)

        }
    }

    #[open]
    #[predicate]
    fn eventually_sat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<a2: Seq<AssignedState>> a2.len() == self.num_vars@ && compatible_inner(a, a2) && self.sat_inner(a2)
        }
    }

    #[open]
    #[predicate]
    fn eventually_sat_complete_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<a2: Seq<AssignedState>> a2.len() == self.num_vars@ && compatible_complete_inner(a, a2) && self.sat_inner(a2)
        }
    }

    #[open]
    #[predicate]
    fn eventually_sat(self, a: Assignments) -> bool {
        pearlite! { self.eventually_sat_inner(a@)}
    }

    #[open]
    #[predicate]
    pub fn sat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self.clauses@.len() ==>
                self.clauses@[i].sat_inner(a)
        }
    }

    #[open]
    #[predicate]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! { formula_sat_inner(self@, a@) }
    }

    #[open]
    #[predicate]
    fn unsat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < self.clauses@.len() &&
                self.clauses@[i].unsat_inner(a)
        }
    }

    #[open]
    #[predicate]
    pub fn unsat(self, a: Assignments) -> bool {
        pearlite! { self.unsat_inner(a@) }
    }

    #[open]
    #[predicate]
    pub fn not_satisfiable(self) -> bool {
        pearlite! { exists<c: Clause> c@.len() == 0 && c.equisat_extension(self) }
    }
}
