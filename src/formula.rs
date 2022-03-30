extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::lit::*;
use crate::clause::*;
use crate::assignments::*;
use crate::logic::*;
use crate::solver_dpll::*;
use crate::watches::*;
use crate::trail::*;

pub struct Formula {
    pub clauses: Vec<Clause>,
    pub num_vars: usize,
}

//#[derive(Copy, Clone, Eq)]
pub enum SatState {
    Unknown,
    Sat,
    Unsat,
}

#[cfg(contracts)]
impl Model for Formula {
    type ModelTy = (Seq<Clause>, Int);

    #[logic]
    fn model(self) -> Self::ModelTy {
        (self.clauses.model(), self.num_vars.model())
    }
}

impl PartialEq for SatState {
    #[trusted] // OK
    fn eq(&self, other: &Self) -> bool {
        return match (self, other) {
            (SatState::Unknown, SatState::Unknown)  => true,
            (SatState::Sat,     SatState::Sat)      => true,
            (SatState::Unsat,   SatState::Unsat)    => true,
            _ => false,
        };
    }
}

#[predicate]
pub fn formula_invariant(f: (Seq<Clause>, Int)) -> bool {
    pearlite! {
        //(@f.clauses).len() > 0 && // added
        forall<i: Int> 0 <= i && i < f.0.len() ==>
            f.0[i].invariant(f.1)
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
        exists<a2 : Seq<AssignedState>> a2.len() === f.1 && complete_inner(a2) && formula_sat_inner(f, a2)
    }
}

#[predicate]
pub fn equisat(f: (Seq<Clause>, Int), o: (Seq<Clause>, Int)) -> bool {
    pearlite! {
        eventually_sat_complete_no_ass(f) === eventually_sat_complete_no_ass(o)
    }
}

#[predicate]
pub fn compatible(f: (Seq<Clause>, Int), o: (Seq<Clause>, Int)) -> bool {
    pearlite! {
        f.1 === o.1 &&
        o.0.len() >= f.0.len() &&
        forall<i: Int> 0 <= i && i < f.0.len() ==>
            (f.0[i]).equals(o.0[i])
        /*
        (@o.clauses).len() >= (@self.clauses).len() &&
        forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
            (@self.clauses)[i] === (@o.clauses)[i]
            */
        /*
            (@(@self.clauses)[i]).len() === (@(@o.clauses)[i]).len() &&
            forall<j: Int> 0 <= j && j < (@(@self.clauses)[i]).len() ==>
            (@(@self.clauses)[i])[j] === (@(@o.clauses)[i])[j]
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
            exists<a2 : Seq<AssignedState>> a2.len() === @self.num_vars && complete_inner(a2) && self.sat_inner(a2)
        }
    }
    #[predicate]
    pub fn equisat(self, o: Formula) -> bool {
        pearlite! {
            self.eventually_sat_complete_no_ass() === o.eventually_sat_complete_no_ass()
        }
    }

    #[predicate]
    pub fn compatible(self, o: Formula) -> bool {
        pearlite! {
            @self.num_vars === @o.num_vars &&
            /*
            (@o.clauses).len() >= (@self.clauses).len() &&
            forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
                (@self.clauses)[i] === (@o.clauses)[i]
                */
            (@o.clauses).len() >= (@self.clauses).len() &&
            forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
                ((@self.clauses)[i]).equals((@o.clauses)[i])
            /*
                (@(@self.clauses)[i]).len() === (@(@o.clauses)[i]).len() &&
                forall<j: Int> 0 <= j && j < (@(@self.clauses)[i]).len() ==>
                (@(@self.clauses)[i])[j] === (@(@o.clauses)[i])[j]
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
            forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
                (@self.clauses)[i].invariant(@self.num_vars)
        }
    }

    #[predicate]
    #[trusted] // OK
    #[ensures(result === self.invariant_old())]
    pub fn invariant(self) -> bool {
        pearlite! {
            //(@f.clauses).len() > 0 && // added
            formula_invariant(@self)
        }
    }

    #[predicate]
    pub fn eventually_sat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<a2 : Seq<AssignedState>> a2.len() === @self.num_vars && compatible_inner(a, a2) && self.sat_inner(a2)
        }
    }

    #[predicate]
    pub fn eventually_sat_complete_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<a2 : Seq<AssignedState>> a2.len() === @self.num_vars && compatible_complete_inner(a, a2) && self.sat_inner(a2)
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
    #[trusted] // OK
    #[ensures(result === self.sat_inner(@a))]
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
}

impl Formula {
    #[trusted] // Only lacking the watcher stuff
    #[requires(self.invariant())]
    #[requires(_t.invariant(*self))]
    #[requires((@clause).len() >= 2)]
    #[requires(vars_in_range_inner(@clause, @self.num_vars))]
    #[requires(no_duplicate_indexes_inner(@clause))]
    #[requires(equisat_extension_inner(clause, @self))]
    #[requires(watches.invariant(*self))] // new
    #[ensures((^watches).invariant(^self))] // new
    #[ensures(@self.num_vars === @(^self).num_vars)]
    #[ensures((^self).invariant())]
    #[ensures(_t.invariant(*self))]
    #[ensures(self.equisat_compatible(^self))]
    #[ensures(@result === (@self.clauses).len())]
    #[ensures((@self.clauses).len() + 1 === (@(^self).clauses).len())]
    //#[ensures(f.eventually_sat(*a) === (^f).eventually_sat(*a))]
    //#[ensures(f.eventually_sat_complete(*a) === (^f).eventually_sat_complete(*a))]
    pub fn add_clause(&mut self, clause: Clause, watches: &mut Watches, _t: &Trail) -> usize {
        let cref = self.clauses.len();
        // Just cbf adding the ensures everywhere. The watch is ok
        proof_assert!(watches.invariant(*self));
        watches.add_watcher(clause.rest[0], cref, self);
        watches.add_watcher(clause.rest[1], cref, self);
        self.clauses.push(clause);
        cref
    }
}

/*
// UNUSED
impl Formula {
    // NONE OF THESE ARE IN USE
    #[trusted] // OK
    #[requires(self.invariant())]
    #[requires(a.invariant(*self))]
    #[ensures(result === self.unsat(*a))]
    pub fn is_unsat(&self, a: &Assignments) -> bool {
        let mut i: usize = 0;
        #[invariant(prev,
            forall<k: Int> 0 <= k && k < @i ==>
            !(@self.clauses)[k].unsat(*a))]
        while i < self.clauses.len() {
            if is_clause_unsat(self, i, a) {
                return true;
            }
            i += 1;
        }
        return false;
    }

    #[trusted] // OK
    #[requires(self.invariant())]
    #[requires(a.invariant(*self))]
    #[ensures(result === self.sat(*a))]
    pub fn is_sat(&self, a: &Assignments) -> bool {
        let mut i: usize = 0;
        #[invariant(prev,
            forall<k: Int> 0 <= k && k < @i ==>
            (@self.clauses)[k].sat(*a))]
        while i < self.clauses.len() {
            if !is_clause_sat(self, i, a) {
                return false;
            }
            i += 1
        }
        return true;
    }

    #[trusted] // OK
    #[requires(self.invariant())]
    #[requires(a.invariant(*self))]
    #[ensures((result === SatState::Sat) === self.sat(*a))]
    #[ensures((result === SatState::Unsat) === self.unsat(*a))]
    #[ensures((result === SatState::Unknown) ==> !a.complete())]
    pub fn eval(&self, a: &Assignments) -> SatState {
        if self.is_sat(a) {
            return SatState::Sat;
        } else if self.is_unsat(a) {
            return SatState::Unsat;
        } else {
            return SatState::Unknown;
        }
    }
}
*/  