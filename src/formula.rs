// Formula is Mac OK with an inline_full + split on VC #12 for add_clause 11.04 22.18
extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{assignments::*, clause::*, lit::*, solver::*, trail::*, watches::*};

#[cfg(feature = "contracts")]
use crate::logic::{
    logic_assignments::*,
    logic_clause::*,
    logic_formula::*,
    logic_trail::*, //tmp?
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
    #[cfg_attr(feature = "trust_formula", trusted)]
    fn eq(&self, other: &Self) -> bool {
        return match (self, other) {
            (SatState::Unknown, SatState::Unknown) => true,
            (SatState::Sat, SatState::Sat) => true,
            (SatState::Unsat, SatState::Unsat) => true,
            _ => false,
        };
    }
}

impl Formula {
    #[cfg_attr(feature = "trust_formula", trusted)]
    #[requires(self.invariant())]
    #[requires(a.invariant(*self))]
    #[requires(@idx < (@self.clauses).len())]
    #[ensures(result === (@self.clauses)[@idx].sat(*a))]
    pub fn is_clause_sat(&self, idx: usize, a: &Assignments) -> bool {
        let clause = &self.clauses[idx];
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

    /*
    #[cfg_attr(feature = "trust_formula", trusted)]
    #[requires(selff.invariant())]
    #[requires(a.invariant(*f))]
    #[requires(@idx < (@self.clauses).len())]
    #[ensures(result === (@self.clauses)[@idx].unsat(*a))]
    pub fn is_clause_unsat(&self, idx: usize, a: &Assignments) -> bool {
        let clause = &self.clauses[idx];
        let mut i: usize = 0;
        #[invariant(previous, forall<j: Int> 0 <= j && j < @i ==> (@clause)[j].unsat(*a))]
        while i < clause.rest.len() {
            if !clause.rest[i].lit_unsat(a) {
                return false;
            }
            i += 1;
        }
        return true;
    }
    */

    // Needs some help on inlining/splitting, but checks out
    #[cfg_attr(feature = "trust_formula", trusted)]
    #[maintains((mut self).invariant())]
    #[maintains(_t.invariant(mut self))]
    #[maintains((mut watches).invariant(mut self))] // new
    #[requires((@clause).len() >= 2)]
    #[requires(@self.num_vars < @usize::MAX/2)]
    #[requires(vars_in_range_inner(@clause, @self.num_vars))]
    #[requires(no_duplicate_indexes_inner(@clause))]
    #[requires(equisat_extension_inner(clause, @self))]
    #[ensures(@self.num_vars === @(^self).num_vars)]
    #[ensures(self.equisat_compatible(^self))]
    #[ensures(self.equisat(^self))] // Added/changed
    #[ensures(@result === (@self.clauses).len())]
    #[ensures((@self.clauses).len() + 1 === (@(^self).clauses).len())]
    pub fn add_clause(&mut self, clause: Clause, watches: &mut Watches, _t: &Trail) -> usize {
        let old_self = Ghost::record(&self);
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
        proof_assert!(^@old_self === ^self);
        proof_assert!((@old_self).equisat_compatible(*self));
        // This is just the trail invariant unwrapped
        proof_assert!(trail_invariant(@_t.trail, *self)); // This one needs some inlining/splits
        cref
    }

    // Passing, but needs the same help as add_clause
    #[cfg_attr(feature = "trust_formula", trusted)]
    #[maintains((mut self).invariant())]
    #[maintains(_t.invariant(mut self))]
    #[requires((@clause).len() == 1)]
    #[requires(clause.invariant(@self.num_vars))]
    #[requires(@self.num_vars < @usize::MAX/2)]
    #[requires(vars_in_range_inner(@clause, @self.num_vars))]
    #[requires(no_duplicate_indexes_inner(@clause))]
    #[requires(equisat_extension_inner(clause, @self))]
    #[ensures(@self.num_vars === @(^self).num_vars)]
    #[ensures(self.equisat_compatible(^self))]
    #[ensures(self.equisat(^self))] // Added/changed
    #[ensures(@result === (@self.clauses).len())]
    #[ensures((@(@(^self).clauses)[@result]).len() == 1)]
    #[ensures((@self.clauses).len() + 1 === (@(^self).clauses).len())]
    pub fn add_unit(&mut self, clause: Clause, _t: &Trail) -> usize {
        let old_self = Ghost::record(&self);
        let cref = self.clauses.len();
        self.clauses.push(clause);
        proof_assert!(^@old_self === ^self);
        proof_assert!((@old_self).equisat_compatible(*self));
        proof_assert!(trail_invariant(@_t.trail, *self)); // This one needs some inlining/splits
        cref
    }

    #[cfg_attr(feature = "trust_formula", trusted)]
    #[requires(self.invariant())]
    #[requires(a.invariant(*self))]
    #[ensures(result === self.sat(*a))]
    pub fn is_sat(&self, a: &Assignments) -> bool {
        let mut i: usize = 0;
        #[invariant(prev, forall<k: Int> 0 <= k && k < @i ==> (@self.clauses)[k].sat(*a))]
        while i < self.clauses.len() {
            if !self.is_clause_sat(i, a) {
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
