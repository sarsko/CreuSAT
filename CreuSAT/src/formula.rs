// Formula is Mac OK with an inline_full + split on VC #12 for add_clause 11.04 22.18

use creusot_contracts::{std::*, Snapshot, *};

use crate::{assignments::*, clause::*, solver::*, trail::*, watches::*};
use ::std::ops::{Index, IndexMut};

#[cfg(creusot)]
use crate::logic::{
    logic::*,
    logic_assignments::*,
    logic_clause::*,
    logic_formula::*,
    logic_trail::*, //tmp?
};

// TODO: Unpub both fields
pub struct Formula {
    pub clauses: Vec<Clause>,
    pub num_vars: usize,
}

impl Index<usize> for Formula {
    type Output = Clause;
    #[inline]
    #[cfg_attr(feature = "trust_formula", trusted)]
    #[requires(ix@ < self@.clauses.len())]
    #[ensures(self@.clauses[ix@] == *result)]
    fn index(&self, ix: usize) -> &Clause {
        #[cfg(not(creusot))]
        unsafe {
            self.clauses.get_unchecked(ix)
        }
        #[cfg(creusot)]
        &self.clauses[ix]
    }
}

impl IndexMut<usize> for Formula {
    #[inline]
    #[cfg_attr(feature = "trust_formula", trusted)]
    #[requires(ix@ < self@.clauses.len())]
    #[ensures(self@.clauses[ix@] == *result)]
    #[ensures((^self)@.clauses[ix@] == ^result)]
    #[ensures(forall<i: Int> 0 <= i && i != ix@ && i < self@.clauses.len() ==> self@.clauses[i] == (^self)@.clauses[i])]
    #[ensures((^self)@.clauses.len() == (*self)@.clauses.len())]
    fn index_mut(&mut self, ix: usize) -> &mut Clause {
        #[cfg(not(creusot))]
        unsafe {
            self.clauses.get_unchecked_mut(ix)
        }
        #[cfg(creusot)]
        &mut self.clauses[ix]
    }
}

impl Formula {
    #[cfg_attr(feature = "trust_formula", trusted)]
    #[ensures(match result {
        SatResult::Sat(assn) => { formula_sat_inner(self@, assn@) },
        SatResult::Unsat     => { self.not_satisfiable() },
        SatResult::Unknown   => { self.inv() && 0 < self.num_vars@ && self.num_vars@ < usize::MAX@/2 },
        SatResult::Err       => { true },
    })]
    pub fn check_formula_invariant(&self) -> SatResult {
        if self.num_vars >= usize::MAX / 2 {
            return SatResult::Err;
        }
        if self.clauses.len() == 0 {
            return SatResult::Sat(Vec::new());
        }
        if self.num_vars == 0 {
            return SatResult::Err; // We have no vars but more than 0 clauses -> error.
        }
        let mut i: usize = 0;
        #[invariant(forall<j: Int> 0 <= j && j < i@ ==> self.clauses@[j].inv(self.num_vars@))]
        #[invariant(forall<j: Int> 0 <= j && j < i@ ==> self.clauses@[j]@.len() > 0)]
        while i < self.clauses.len() {
            if !self.clauses[i].check_clause_invariant(self.num_vars) {
                return SatResult::Err;
            }
            if self.clauses[i].len() == 0 {
                return SatResult::Unsat;
            }
            i += 1;
        }
        SatResult::Unknown
    }

    #[cfg_attr(feature = "trust_formula", trusted)]
    #[requires(self.inv())]
    #[requires(a.inv(*self))]
    #[requires(idx@ < self.clauses@.len())]
    #[ensures(result == self.clauses@[idx@].sat(*a))]
    pub fn is_clause_sat(&self, idx: usize, a: &Assignments) -> bool {
        let clause = &self.clauses[idx];
        let mut i: usize = 0;
        #[invariant(forall<j: Int> 0 <= j && j < i@ ==> !clause@[j].sat(*a))]
        while i < clause.len() {
            if clause[i].lit_sat(a) {
                return true;
            }
            i += 1;
        }
        false
    }

    #[cfg_attr(feature = "trust_formula", trusted)]
    #[maintains((mut self).inv())]
    #[maintains(_t.inv(mut self))]
    #[maintains((mut watches).inv(mut self))]
    #[requires((clause@).len() >= 2)]
    #[requires(self.num_vars@ < usize::MAX@/2)]
    //#[requires(vars_in_range_inner(clause@, self.num_vars@))]
    //#[requires(no_duplicate_indexes_inner(clause@))]
    #[requires(clause.inv(self.num_vars@))]
    #[requires(equisat_extension_inner(clause, self@))]
    #[ensures(self.num_vars@ == (^self).num_vars@)]
    #[ensures(self.equisat(^self))]
    #[ensures(result@ == self.clauses@.len())]
    #[ensures((^self).clauses@[result@] == clause)]
    #[ensures(self.clauses@.len() + 1 == (^self).clauses@.len())]
    pub fn add_clause(&mut self, clause: Clause, watches: &mut Watches, _t: &Trail) -> usize {
        let old_self: Snapshot<&mut Formula> = snapshot! { self };
        let cref = self.clauses.len();
        // The weird assignment to first_/second_lit is because otherwise we break the precond for
        // add_watcher that the cref should be less than f.clauses.len(). We can't update the watches
        // after the clause is added, as the value gets moved by the push. Could of course index on last
        // element of f.clauses after the push, but I prefer this.
        let first_lit = clause[0];
        let second_lit = clause[1];
        self.clauses.push(clause);
        watches.add_watcher(first_lit, cref, self, second_lit);
        watches.add_watcher(second_lit, cref, self, first_lit);
        proof_assert!(^old_self.inner() == ^self);
        //proof_assert!(old_self.equisat_compatible(*self));
        proof_assert!(old_self.equisat(*self));
        proof_assert!(trail_invariant(_t.trail@, *self)); // This one needs some inlining/splits
        cref
    }

    #[cfg_attr(feature = "trust_formula", trusted)]
    #[maintains((mut self).inv())]
    #[maintains(_t.inv(mut self))]
    #[maintains((mut watches).inv(mut self))]
    #[requires(clause@.len() >= 2)]
    #[requires(self.num_vars@ < usize::MAX@/2)]
    #[requires(clause.inv(self.num_vars@))]
    #[requires(equisat_extension_inner(clause, self@))]
    #[ensures(self.num_vars@ == (^self).num_vars@)]
    #[ensures(self.equisat(^self))]
    #[ensures(result@ == self.clauses@.len())]
    #[ensures((^self).clauses@[result@] == clause)]
    #[ensures(self.clauses@.len() + 1 == (^self).clauses@.len())]
    pub fn add_unwatched_clause(&mut self, clause: Clause, watches: &mut Watches, _t: &Trail) -> usize {
        let old_self: Snapshot<&mut Formula> = snapshot! { self };
        let cref = self.clauses.len();
        self.clauses.push(clause);
        cref
    }

    #[cfg_attr(feature = "trust_formula", trusted)]
    #[maintains((mut self).inv())]
    #[maintains(_t.inv(mut self))]
    #[requires((clause@).len() == 1)]
    #[requires(clause.inv(self.num_vars@))]
    #[requires(self.num_vars@ < usize::MAX@/2)]
    #[requires(vars_in_range_inner(clause@, self.num_vars@))]
    #[requires(no_duplicate_indexes_inner(clause@))]
    #[requires(equisat_extension_inner(clause, self@))]
    #[ensures(self.num_vars@ == (^self).num_vars@)]
    //#[ensures(self.equisat_compatible(^self))]
    #[ensures(forall<i: Int> 0 <= i && i < self.clauses@.len() ==> self.clauses@[i] == (^self).clauses@[i])] // This or equisat_compatible is needed for the watch invariant.
    #[ensures(self.equisat(^self))] // Added/changed
    #[ensures(result@ == self.clauses@.len())]
    #[ensures((^self).clauses@[result@]@.len() == 1)]
    #[ensures(self.clauses@.len() + 1 == (^self).clauses@.len())]
    pub fn add_unit(&mut self, clause: Clause, _t: &Trail) -> usize {
        let old_self: Snapshot<&mut Formula> = snapshot! { self };
        let cref = self.clauses.len();
        self.clauses.push(clause);
        cref
    }

    #[cfg_attr(feature = "trust_formula", trusted)]
    #[requires(self.inv())]
    #[requires(a.inv(*self))]
    #[ensures(result == self.sat(*a))]
    pub fn is_sat(&self, a: &Assignments) -> bool {
        let mut i: usize = 0;
        #[invariant(forall<k: Int> 0 <= k && k < i@ ==> self.clauses@[k].sat(*a))]
        while i < self.clauses.len() {
            if !self.is_clause_sat(i, a) {
                return false;
            }
            i += 1
        }
        true
    }

    #[cfg_attr(feature = "trust_formula", trusted)]
    #[maintains((mut watches).inv(mut self))]
    #[maintains((mut self).inv())]
    #[maintains((*t).inv(mut self))]
    #[requires(self.num_vars@ < usize::MAX@/2)]
    #[requires(self.clauses@[cref@]@.len() > 1)]
    #[requires(cref@ < self.clauses@.len())]
    #[ensures(self.equisat(^self))]
    #[ensures(self.num_vars == (^self).num_vars)]
    fn delete_clause(&mut self, cref: usize, watches: &mut Watches, t: &Trail) {
        let old_f: Snapshot<&mut Formula> = snapshot! { self };
        watches.unwatch(self, t, cref, self.clauses[cref][0]);
        watches.unwatch(self, t, cref, self.clauses[cref][1]);
        self.clauses[cref].deleted = true;
        proof_assert!(forall<i: Int> 0 <= i && i < self.clauses@[cref@]@.len() ==>
            self.clauses@[cref@]@[i] == old_f.clauses@[cref@]@[i]);
        proof_assert!(old_f.equisat(*self)); // This assertion helps with the invariant, which otherwise takes a long time.
        proof_assert!(^self == ^old_f.inner());
    }

    // OK
    #[cfg_attr(feature = "trust_formula", trusted)]
    #[maintains((mut self).inv())]
    #[maintains((mut watches).inv(mut self))]
    #[maintains((*t).inv(mut self))]
    #[requires(t.inv(*self))]
    #[requires(self.num_vars@ < usize::MAX@/2)]
    #[ensures(self.num_vars == (^self).num_vars)]
    #[ensures(self.equisat(^self))]
    pub fn delete_clauses(&mut self, watches: &mut Watches, t: &Trail) {
        let old_f: Snapshot<&mut Formula> = snapshot! { self };
        let old_w: Snapshot<&mut Watches> = snapshot! { watches };
        // unwatch trivially SAT
        let mut i = 0;
        #[invariant(watches.inv(*self))]
        #[invariant(t.inv(*self))]
        #[invariant(self.inv())]
        #[invariant(self.num_vars@ == old_f.num_vars@)]
        #[invariant(self.equisat(*old_f.inner()))]
        while i < self.clauses.len() {
            if !self.clauses[i].deleted {
                proof_assert!(t.assignments.inv(*self));
                if self.clauses[i].len() > 1 && self.is_clause_sat(i, &t.assignments) {
                    self.delete_clause(i, watches, t);
                }
            }
            i += 1;
        }

        // Ideally remove UNSAT lits
    }

    #[cfg_attr(feature = "trust_formula", trusted)]
    #[maintains((mut self).inv())]
    #[maintains((mut watches).inv(mut self))]
    //#[maintains((*t).inv(mut self))]
    #[requires(self.num_vars@ < usize::MAX@/2)]
    #[requires(t.inv(*self))]
    #[ensures(t.inv(^self))]
    #[ensures(self.num_vars == (^self).num_vars)]
    #[ensures(self.equisat(^self))]
    pub fn simplify_formula(&mut self, watches: &mut Watches, t: &Trail) {
        // unwatch trivially SAT
        self.delete_clauses(watches, t);
        // Ideally remove UNSAT lits
    }

    #[cfg_attr(feature = "trust_formula", trusted)]
    #[maintains((mut self).inv())]
    #[maintains((mut watches).inv(mut self))]
    //#[maintains((*t).inv(mut self))]
    #[requires(self.inv())]
    #[requires(t.inv(*self))]
    #[ensures(t.inv(^self))]
    #[requires(self.num_vars@ < usize::MAX@/2)]
    #[ensures(self.num_vars == (^self).num_vars)]
    #[ensures(self.equisat(^self))]
    pub fn reduceDB(&mut self, watches: &mut Watches, t: &Trail, s: &mut Solver) {
        // Okay now I understand why MicroSat does this "weirdly"
        while s.num_lemmas > s.max_lemmas {
            if usize::MAX - 300 > s.max_lemmas {
                s.max_lemmas += 300;
            } else {
                break;
            }
        }
        //s.num_lemmas = 0;
        let mut i = s.initial_len;
        let old_f: Snapshot<&mut Formula> = snapshot! { self };
        let old_w: Snapshot<&mut Watches> = snapshot! { watches };
        #[invariant(watches.inv(*self))]
        #[invariant(t.inv(*self))]
        #[invariant(self.inv())]
        #[invariant(self.num_vars@ == old_f.num_vars@)]
        #[invariant(self.equisat(*old_f.inner()))]
        while i < self.clauses.len() {
            if !self.clauses[i].deleted {
                //if self.clauses[i].len() > 12 {
                if self.clauses[i].len() > 6 {
                    let mut cnt = 0;
                    let mut j = 0;
                    while j < self.clauses[i].len() && cnt < 6 {
                        if self.clauses[i][j].lit_sat(&t.assignments) {
                            cnt += 1;
                        }
                        j += 1;
                    }
                    if cnt >= 6 {
                        // Maybe add the invariant that nlemmas keeps track of the number of lemmas lol
                        if s.num_lemmas > 0 {
                            s.num_lemmas -= 1;
                        }
                        self.delete_clause(i, watches, t);
                    }
                }
            }
            i += 1;
        }
    }
}
