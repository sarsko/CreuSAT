use creusot_contracts::prelude::*;

use crate::{assignments::*, clause::*, lit::*};

// ===== Formula =====
pub struct Formula {
    pub clauses: Vec<Clause>,
    pub num_vars: usize,
}

#[cfg(creusot)]
impl View for Formula {
    type ViewTy = (Seq<Clause>, Int);

    #[logic(open)]
    fn view(self) -> Self::ViewTy {
        (self.clauses.view(), self.num_vars.view())
    }
}

#[logic(open)]
pub fn formula_invariant(f: (Seq<Clause>, Int)) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < f.0.len() ==>
            (f.0[i].inv(f.1) && f.0[i]@.len() > 0)
    }
}

#[logic(open)]
pub fn formula_sat_inner(f: (Seq<Clause>, Int), a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < f.0.len() ==>
            f.0[i].sat_inner(a)
    }
}

#[logic(open)]
pub fn eventually_sat_complete(f: (Seq<Clause>, Int)) -> bool {
    pearlite! {
        exists<a2: Seq<AssignedState>> a2.len() == f.1 && complete_inner(a2) && formula_sat_inner(f, a2)
    }
}

#[logic(open)]
fn equisat(f: (Seq<Clause>, Int), o: (Seq<Clause>, Int)) -> bool {
    pearlite! {
        eventually_sat_complete(f) == eventually_sat_complete(o)
    }
}

// Predicates
impl Formula {
    #[logic(open)]
    pub fn eventually_sat_complete(self) -> bool {
        pearlite! {
            exists<a2: Seq<AssignedState>> a2.len() == self.num_vars@ && complete_inner(a2) && self.sat_inner(a2)
        }
    }

    #[logic(open)]
    pub fn equisat(self, o: Formula) -> bool {
        self.eventually_sat_complete() == o.eventually_sat_complete()
    }

    #[logic(open)]
    #[cfg_attr(feature = "trust_formula_logic", trusted)]
    #[ensures(result == self.inv_mirror())] // Removing this makes a bunch of seemingly unrelated things fail
    pub fn inv(self) -> bool {
        pearlite! { formula_invariant(self@) }
    }

    #[logic(open)]
    pub fn inv_mirror(self) -> bool {
        pearlite! {
            (forall<i: Int> 0 <= i && i < self.clauses@.len() ==>
                self.clauses@[i].inv(self.num_vars@))
            &&
            (forall<i: Int> 0 <= i && i < self.clauses@.len() ==>
                self.clauses@[i]@.len() >= 1)

        }
    }

    #[logic(open)]
    pub fn eventually_sat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<a2: Seq<AssignedState>> a2.len() == self.num_vars@ && compatible_inner(a, a2) && self.sat_inner(a2)
        }
    }

    #[logic(open)]
    fn eventually_sat_complete_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<a2: Seq<AssignedState>> a2.len() == self.num_vars@ && compatible_complete_inner(a, a2) && self.sat_inner(a2)
        }
    }

    #[logic(open)]
    pub fn eventually_sat(self, a: Assignments) -> bool {
        pearlite! { self.eventually_sat_inner(a@)}
    }

    #[logic(open)]
    pub fn sat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self.clauses@.len() ==>
                self.clauses@[i].sat_inner(a)
        }
    }

    #[logic(open)]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! { formula_sat_inner(self@, a@) }
    }

    #[logic(open)]
    pub fn unsat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < self.clauses@.len() &&
                self.clauses@[i].unsat_inner(a)
        }
    }

    #[logic(open)]
    pub fn unsat(self, a: Assignments) -> bool {
        pearlite! { self.unsat_inner(a@) }
    }

    #[logic(open)]
    pub fn not_satisfiable(self) -> bool {
        pearlite! { exists<c: Clause> c@.len() == 0 && c.equisat_extension(self) }
    }
}
