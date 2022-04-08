extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::{
    assignments::*,
    clause::*,
    lit::*,
    solver::*,
    trail::*,
    watches::*,
};

#[cfg(contracts)]
use crate::logic::{
    logic_assignments::*,
    logic_clause::*,
    logic_formula::*,
};

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


#[trusted] // OK // zzTODOzz check if this can be moved to clause
#[ensures(result === (@f.clauses)[@idx].sat(*a))]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(@idx < (@f.clauses).len())]
pub fn is_clause_sat(f: &Formula, idx: usize, a: &Assignments) -> bool {
    let clause = &f.clauses[idx];
    let mut i: usize = 0;
    #[invariant(previous, forall<j: Int> 0 <= j && j < @i ==> !(@clause)[j].sat(*a))]
    while i < clause.rest.len() {
        if clause.rest[i].lit_sat(a) {
            return true;
        }
        i += 1;
    }
    return false;
}

impl Formula {
    #[trusted] // OK[04.04]
    #[requires(@self.num_vars < @usize::MAX/2)]
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
        // The weird assignment to first_/second_lit is because otherwise we break the precond for
        // add_watcher that the cref should be less than f.clauses.len(). We can't update the watches
        // after the clause is added, as the value gets moved by the push. Could of course index on last
        // element of f.clauses after the push, but I prefer this.
        let first_lit = clause.rest[0];
        let second_lit = clause.rest[1];
        self.clauses.push(clause);
        watches.add_watcher(first_lit, cref, self);
        watches.add_watcher(second_lit, cref, self);
        cref
    }
    #[trusted] // OK[04.04]
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