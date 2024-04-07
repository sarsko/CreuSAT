extern crate creusot_contracts;
#[allow(unused)]
use creusot_contracts::{model::*, std::*, *};

use crate::{clause::*, decision::*, formula::*};

#[cfg(creusot)]
use crate::logic::*;

pub type AssignedState = u8;

pub struct Assignments(pub Vec<AssignedState>, pub usize);

#[cfg(creusot)]
impl ShallowModel for Assignments {
    type ShallowModelTy = Seq<AssignedState>;

    #[logic]
    #[open]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.0.shallow_model()
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

#[predicate]
#[open]
pub fn assignments_invariant(a: Seq<AssignedState>, f: Formula) -> bool {
    pearlite! { f.num_vars@ == a.len() }
}

// Predicates
impl Assignments {
    #[predicate]
    #[open]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            f.num_vars@ == self@.len() && self.1@ <= f.num_vars@
        }
    }

    #[predicate]
    #[open]
    pub fn compatible(self, a2: Assignments) -> bool {
        pearlite! { compatible_inner(self@, a2@) }
    }

    #[predicate]
    #[open]
    pub fn complete(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self@.len() ==> !unset(self@[i])
        }
    }

    #[predicate]
    #[open]
    pub fn compatible_complete(self, a2: Assignments) -> bool {
        self.compatible(a2) && a2.complete()
    }
}

impl Assignments {
    #[cfg_attr(feature = "trust_assignments", trusted)]
    #[ensures(forall<i: Int> 0 <= i && i < self@.len() ==> self@[i] == result@[i])]
    #[ensures(self@.len() == result@.len())]
    #[ensures(result.1@ == self.1@)]
    pub fn clone(&self) -> Self {
        let mut out = Vec::new();
        let mut i: usize = 0;
        #[invariant(i@ <= self@.len())]
        #[invariant(forall<j: Int> 0 <= j && j < i@ ==> out@[j] == self@[j])]
        #[invariant(out@.len() == i@)]
        while i < self.0.len() {
            out.push(self.0[i]);
            i += 1;
        }
        Assignments(out, self.1)
    }

    #[cfg_attr(feature = "trust_assignments", trusted)]
    #[requires(f.invariant())]
    #[ensures(result.invariant(*f))]
    #[ensures(forall<i: Int> 0 <= i && i < result@.len() ==> unset(result@[i]))]
    pub fn new(f: &Formula) -> Self {
        Assignments(vec::from_elem(2u8, f.num_vars), 0)
    }

    #[cfg_attr(feature = "trust_assignments", trusted)]
    #[maintains((mut self).invariant(*_f))]
    #[requires(!self.complete())]
    #[requires(d.invariant(self@.len()))]
    #[ensures(result@ < self@.len() && unset(self@[result@]))]
    #[ensures(self@ == (^self)@)]
    pub fn find_unassigned(&mut self, d: &Decisions, _f: &Formula) -> usize {
        let mut i: usize = self.1;
        #[invariant(i@ <= d.lit_order@.len())]
        while i < d.lit_order.len() {
            let curr = self.0[d.lit_order[i]];
            if curr >= 2 {
                self.1 = i + 1;
                return d.lit_order[i];
            }
            i += 1;
        }
        // Strictly speaking this is an unecessary runtime check, but it only gets run at most once and it
        // greatly simplifies the proof.
        i = 0;
        #[invariant(forall<j: Int> 0 <= j && j < i@ ==> !unset(self@[j]))]
        while i < self.0.len() {
            if self.0[i] >= 2 {
                return i;
            }
            i += 1;
        }
        unreachable!();
    }

    #[cfg_attr(feature = "trust_assignments", trusted)]
    #[maintains((mut self).invariant(*f))]
    #[requires(f.invariant())]
    #[requires(0 <= i@ && i@ < f.clauses@.len())]
    #[ensures((*self).compatible(^self))]
    #[ensures(f.eventually_sat_complete(*self) == f.eventually_sat_complete(^self))]
    /*
    #[ensures((result == ClauseState::Unit)    ==> f.clauses@[i@].unit(*self) && !(self).complete())]
    #[ensures((result == ClauseState::Sat)     ==> f.clauses@[i@].sat(^self) && self@ == @^self)]
    #[ensures((result == ClauseState::Unsat)   ==> f.clauses@[i@].unsat(^self) && self@ == @^self)]
    #[ensures((result == ClauseState::Unknown) ==> self@ == @^self && !(^self).complete())]
    */
    #[ensures(match result {
        ClauseState::Unit => f.clauses@[i@].unit(*self) && !self.complete(),
        ClauseState::Sat => f.clauses@[i@].sat(^self) && self@ == (^self)@,
        ClauseState::Unsat => f.clauses@[i@].unsat(^self) && self@ == (^self)@,
        ClauseState::Unknown => self@ == (^self)@ && !(^self).complete(),
    })]
    #[ensures((self).complete() ==> *self == ^self && ((result == ClauseState::Unsat) || (result == ClauseState::Sat)))]
    pub fn unit_prop_once(&mut self, i: usize, f: &Formula) -> ClauseState {
        let clause = &f.clauses[i];
        let _old_a: Snapshot<&mut Assignments> = snapshot!(self);
        match clause.check_if_unit(self, f) {
            ClauseState::Unit => {
                // I tried both to make ClauseState::Unit contain a usize and to return a tuple, but
                // both were slower than getting it after. Kind of makes sense since unit clauses are
                // rare and we on average have to traverse n/2 lits to find the unit lit. If I make formula
                // mutable, then I can swap to index 0 and skip the call to clause.get_unit()
                let lit = clause.get_unit(self, f);
                proof_assert!(lemma_unit_wrong_polarity_unsat_formula(*clause, *f, self@, lit.index_logic(), bool_to_assignedstate(lit.polarity)); true);
                proof_assert!(lemma_unit_forces(*f, self@, lit.index_logic(), bool_to_assignedstate(lit.polarity)); true);
                if lit.polarity {
                    self.0[lit.index()] = 1;
                } else {
                    self.0[lit.index()] = 0;
                }
                proof_assert!(lemma_extension_sat_base_sat(*f, _old_a.inner()@, lit.index_logic(), bool_to_assignedstate(lit.polarity)); true);
                proof_assert!(lemma_extensions_unsat_base_unsat(_old_a.inner()@, lit.index_logic(), *f); true);
                proof_assert!(^self == ^_old_a.inner());
                return ClauseState::Unit;
            }
            o => return o,
        }
    }

    #[cfg_attr(feature = "trust_assignments", trusted)]
    #[maintains((mut self).invariant(*f))]
    #[requires(f.invariant())]
    #[ensures(f.eventually_sat_complete(^self) == f.eventually_sat_complete(*self))]
    #[ensures((*self).compatible(^self))]
    #[ensures(match result {
        ClauseState::Sat => f.sat(^self),
        ClauseState::Unsat => f.unsat(^self),
        ClauseState::Unknown => !(^self).complete(),
        ClauseState::Unit => !self.complete(),
    })]
    #[ensures((self).complete() ==> *self == (^self) && ((result == ClauseState::Unsat) || f.sat(*self)))]
    pub fn unit_propagate(&mut self, f: &Formula) -> ClauseState {
        let _old_a: Snapshot<&mut Assignments> = snapshot!(self);
        let mut i: usize = 0;
        let mut out = ClauseState::Sat;
        #[invariant(self.invariant(*f))]
        #[invariant(_old_a.compatible(*self))]
        #[invariant(f.eventually_sat_complete(*_old_a.inner()) == f.eventually_sat_complete(*self))]
        #[invariant(!(out == ClauseState::Unsat))]
        #[invariant(_old_a.complete() ==> *_old_a.inner() == *self && forall<j: Int> 0 <= j && j < i@ ==>
            !f.clauses@[j].unknown(*self) && !f.clauses@[j].unit(*self) && f.clauses@[j].sat(*self)
        )]
        #[invariant(out == ClauseState::Sat ==> forall<j: Int> 0 <= j && j < i@ ==>
            !f.clauses@[j].unsat(*self) && !f.clauses@[j].unknown(*self) && !f.clauses@[j].unit(*self) && f.clauses@[j].sat(*self)
        )]
        #[invariant(out == ClauseState::Unit ==> !_old_a.complete())]
        #[invariant(out == ClauseState::Unknown ==> !self.complete())]
        while i < f.clauses.len() {
            match self.unit_prop_once(i, f) {
                ClauseState::Sat => {}
                ClauseState::Unsat => {
                    return ClauseState::Unsat;
                }
                ClauseState::Unit => {
                    out = ClauseState::Unit;
                }
                ClauseState::Unknown => match out {
                    ClauseState::Sat => {
                        out = ClauseState::Unknown;
                    }
                    _ => {}
                },
            }
            i += 1
        }
        return out;
    }

    #[cfg_attr(feature = "trust_assignments", trusted)]
    #[requires(f.invariant())]
    #[maintains((mut self).invariant(*f))]
    #[ensures(f.eventually_sat_complete(*self) == f.eventually_sat_complete(^self))]
    #[ensures((*self).compatible(^self))]
    #[ensures(result == Some(false) ==> f.unsat(^self))]
    #[ensures(result == Some(true) ==> f.sat(^self))]
    #[ensures(result == None ==> !(^self).complete())]
    pub fn do_unit_propagation(&mut self, f: &Formula) -> Option<bool> {
        let _old_a: Snapshot<&mut Assignments> = snapshot!(self);
        #[invariant(self.invariant(*f))]
        #[invariant(_old_a.compatible(*self))]
        #[invariant(f.eventually_sat_complete(*_old_a.inner()) ==> f.eventually_sat_complete(*self))]
        loop {
            match self.unit_propagate(f) {
                ClauseState::Sat => {
                    return Some(true);
                }
                ClauseState::Unsat => {
                    return Some(false);
                }
                ClauseState::Unknown => {
                    return None;
                }
                ClauseState::Unit => {} // Continue
            }
        }
    }
}
