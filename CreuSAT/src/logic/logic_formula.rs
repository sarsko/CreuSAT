extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{
    assignments::*,
    clause::*,
    formula::*,
    lit::*,
    trail::*,
    //solver_dpll::*,
    watches::*,
};

use crate::logic::{logic::*, logic_assignments::*};

#[cfg(feature = "contracts")]
impl Model for Formula {
    type ModelTy = (Seq<Clause>, Int);

    #[logic]
    fn model(self) -> Self::ModelTy { (self.clauses.model(), self.num_vars.model()) }
}

#[predicate]
pub fn formula_invariant(f: (Seq<Clause>, Int)) -> bool {
    pearlite! {
        //(@f.clauses).len() > 0 && // added
        (forall<i: Int> 0 <= i && i < f.0.len() ==>
            f.0[i].invariant(f.1))
        &&
        // Added, will break stuff
        (forall<i: Int> 0 <= i && i < f.0.len() ==>
            (@f.0[i]).len() > 0)
    }
}

#[predicate]
pub fn formula_sat_inner(f: (Seq<Clause>, Int), a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < f.0.len() ==>
            f.0[i].sat_inner(a)
    }
}

#[predicate]
pub fn eventually_sat_complete_no_ass(f: (Seq<Clause>, Int)) -> bool {
    pearlite! {
        exists<a2 : Seq<AssignedState>> a2.len() == f.1 && complete_inner(a2) && formula_sat_inner(f, a2)
    }
}

#[predicate]
pub fn equisat(f: (Seq<Clause>, Int), o: (Seq<Clause>, Int)) -> bool {
    pearlite! {
        eventually_sat_complete_no_ass(f) == eventually_sat_complete_no_ass(o)
    }
}

#[predicate]
pub fn compatible(f: (Seq<Clause>, Int), o: (Seq<Clause>, Int)) -> bool {
    pearlite! {
        f.1 == o.1 &&
        o.0.len() >= f.0.len() &&
        forall<i: Int> 0 <= i && i < f.0.len() ==>
            (f.0[i]).equals(o.0[i])
        /*
        (@o.clauses).len() >= (@self.clauses).len() &&
        forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
            (@self.clauses)[i] == (@o.clauses)[i]
            */
        /*
            (@(@self.clauses)[i]).len() == (@(@o.clauses)[i]).len() &&
            forall<j: Int> 0 <= j && j < (@(@self.clauses)[i]).len() ==>
            (@(@self.clauses)[i])[j] == (@(@o.clauses)[i])[j]
            */
    }
}

#[predicate]
pub fn equisat_compatible_inner(f: (Seq<Clause>, Int), o: (Seq<Clause>, Int)) -> bool {
    pearlite! {
        compatible(f, o) && equisat(f, o)
    }
}

// Predicates
impl Formula {
    // New stuff:
    #[predicate]
    pub fn eventually_sat_complete_no_ass(self) -> bool {
        pearlite! {
            exists<a2 : Seq<AssignedState>> a2.len() == @self.num_vars && complete_inner(a2) && self.sat_inner(a2)
        }
    }
    #[predicate]
    pub fn equisat(self, o: Formula) -> bool {
        pearlite! {
            self.eventually_sat_complete_no_ass() == o.eventually_sat_complete_no_ass()
        }
    }

    #[predicate]
    pub fn compatible(self, o: Formula) -> bool {
        pearlite! {
            @self.num_vars == @o.num_vars &&
            /*
            (@o.clauses).len() >= (@self.clauses).len() &&
            forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
                (@self.clauses)[i] == (@o.clauses)[i]
                */
            (@o.clauses).len() >= (@self.clauses).len() &&
            forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
                ((@self.clauses)[i]).equals((@o.clauses)[i])
            /*
                (@(@self.clauses)[i]).len() == (@(@o.clauses)[i]).len() &&
                forall<j: Int> 0 <= j && j < (@(@self.clauses)[i]).len() ==>
                (@(@self.clauses)[i])[j] == (@(@o.clauses)[i])[j]
                */
        }
    }

    #[predicate]
    pub fn equisat_compatible(self, o: Formula) -> bool {
        pearlite! {
            equisat_compatible_inner(@self, @o)
            /*
            self.compatible(o) &&
            self.equisat(o)
            */
        }
    }

    #[predicate]
    pub fn invariant_old(self) -> bool {
        pearlite! {
            //(@f.clauses).len() > 0 && // added
            (forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
                (@self.clauses)[i].invariant(@self.num_vars))
            &&
            (forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
                (@(@self.clauses)[i]).len() >= 1)

        }
    }

    #[predicate]
    #[cfg_attr(feature = "trust_formula_logic", trusted)]
    #[ensures(result == self.invariant_old())]
    pub fn invariant(self) -> bool {
        pearlite! {
            //(@f.clauses).len() > 0 && // added
            formula_invariant(@self)
            //&& @self.num_vars < @usize::MAX/2 // Added this as it ends up being a pervasive condition otherwise
        }
    }

    #[predicate]
    pub fn eventually_sat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<a2 : Seq<AssignedState>> a2.len() == @self.num_vars && compatible_inner(a, a2) && self.sat_inner(a2)
        }
    }

    #[predicate]
    pub fn eventually_sat_complete_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<a2 : Seq<AssignedState>> a2.len() == @self.num_vars && compatible_complete_inner(a, a2) && self.sat_inner(a2)
        }
    }

    #[predicate]
    pub fn eventually_sat_complete(self, a: Assignments) -> bool {
        pearlite! { self.eventually_sat_complete_inner(@a)}
    }

    #[predicate]
    pub fn eventually_sat(self, a: Assignments) -> bool {
        pearlite! { self.eventually_sat_inner(@a)}
    }

    #[predicate]
    pub fn sat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
                (@self.clauses)[i].sat_inner(a)
        }
    }

    #[predicate]
    #[cfg_attr(feature = "trust_formula_logic", trusted)]
    #[ensures(result == self.sat_inner(@a))]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! {
            //self.sat_inner(@a)
            formula_sat_inner(@self, @a)
        }
    }

    #[predicate]
    pub fn unsat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@self.clauses).len() &&
                (@self.clauses)[i].unsat_inner(a)
        }
    }

    #[predicate]
    pub fn unsat(self, a: Assignments) -> bool {
        pearlite! {
            self.unsat_inner(@a)
        }
    }

    #[predicate]
    pub fn not_satisfiable(self) -> bool {
        pearlite! {
            exists<c: Clause> (@c).len() == 0
            && c.equisat_extension(self)
        }
    }
}
