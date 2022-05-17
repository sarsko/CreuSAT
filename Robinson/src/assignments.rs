
extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::clause::*;
use crate::decision::*;
use crate::formula::*;
use crate::lit::*;
use crate::logic::*;

pub type AssignedState = u8;

pub struct Assignments(pub Vec<AssignedState>, pub usize);

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
    }
}

// Predicates
impl Assignments {
    #[predicate]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            @f.num_vars === (@self).len() && @self.1 <= @f.num_vars
        }
    }

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

impl Assignments {
    #[cfg_attr(feature = "trust_assignments", trusted)]
    #[ensures(forall<i: Int> 0 <= i && i < (@self).len() ==> (@self)[i] === (@result)[i])]
    #[ensures((@self).len() === (@result).len())]
    #[ensures(@result.1 === @self.1)]
    //#[ensures(*self == result)] // This is broken
    pub fn clone(&self) -> Self {
        let mut out = Vec::new();
        let mut i: usize = 0;
        #[invariant(loop_invariant, 0 <= @i && @i <= (@self).len())]
        #[invariant(equality, forall<j: Int> 0 <= j && j < @i ==> (@out)[j] === (@self)[j])]
        #[invariant(len, (@out).len() === @i)]
        while i < self.0.len() {
            let curr = self.0[i];
            //out.push(curr.clone());
            out.push(curr);
            i += 1;
        }
        proof_assert!((@out).len() == (@self).len());
        proof_assert!(forall<j: Int> 0 <= j && j < (@self).len() ==> (@out)[j] === (@self)[j]);
        //proof_assert!(out == self.0);
        Assignments(out, self.1)
    }

    /*
    #[cfg_attr(feature = "trust_assignments", trusted)]
    #[requires(lit.invariant(@_f.num_vars))]
    #[requires(_f.invariant())]
    #[requires(self.invariant(*_f))]
    #[requires(unset((@self)[@lit.idx]))] // Added, will break stuff further up
    //#[ensures(self.compatible(^self))]
    #[ensures((^self).invariant(*_f))]
    #[ensures(@(@^self)[@lit.idx] === 1 || @(@^self)[@lit.idx] === 0)]
    #[ensures((@^self).len() === (@self).len())]
    #[ensures((forall<j : Int> 0 <= j && j < (@self).len() &&
        j != @lit.idx ==> (@*self)[j] === (@^self)[j]))]
    #[ensures(
        match lit.polarity {
            true => @(@^self)[@lit.idx] === 1,
            false => @(@^self)[@lit.idx] === 0,
        }
    )]
    pub fn set_assignment(&mut self, lit: Lit, _f: &Formula) {
        let old_self = Ghost::record(&self);

        proof_assert!(self.invariant(*_f));
        proof_assert!(_f.invariant());
        proof_assert!(lit.invariant(@_f.num_vars));
        proof_assert!(unset((@self)[@lit.idx]));

        if lit.polarity {
            self.0[lit.idx] = 1;
            //proof_assert!(@self === (@@old_self).set(@lit.idx, 1u8));
        } else {
            self.0[lit.idx] = 0;
            //proof_assert!(@self === (@@old_self).set(@lit.idx, 0u8));
        }
        proof_assert!(^@old_self === ^self);
        //self.0[l.idx] = l.polarity as u8;
    }
    */

    #[cfg_attr(feature = "trust_assignments", trusted)]
    #[requires(f.invariant())]
    #[ensures(result.invariant(*f))]
    pub fn new(f: &Formula) -> Self {
        Assignments(vec::from_elem(2u8, f.num_vars), 0)
        /*
        let mut assign: Vec<AssignedState> = Vec::new();
        let mut i: usize = 0;
        #[invariant(loop_invariant, 0 <= @i && @i <= @f.num_vars)]
        #[invariant(length_invariant, (@assign).len() === @i)]
        while i < f.num_vars {
            assign.push(2);
            i += 1
        }
        Assignments(assign, 0)
        */
    }

    //#[requires(self.invariant(*_f))]
    //#[ensures((^self).invariant(*_f))]
    #[cfg_attr(feature = "trust_assignments", trusted)]
    #[maintains((mut self).invariant(*_f))]
    #[requires(!self.complete())]
    #[requires(d.invariant((@self).len()))]
    #[ensures(@result < (@self).len() && unset((@self)[@result]))]
    #[ensures(@self === @^self)]
    pub fn find_unassigned(&mut self, d: &Decisions, _f: &Formula) -> usize {
        let mut i: usize = self.1;
        #[invariant(i_bound, @i <= (@d.lit_order).len())]
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
        #[invariant(prev, forall<j: Int> 0 <= j && j < @i ==> !unset((@self)[j]))]
        while i < self.0.len() {
            if self.0[i] >= 2 {
                return i;
            }
            i += 1;
        }
        panic!();
    }

    #[cfg_attr(feature = "trust_assignments", trusted)]
    #[maintains((mut self).invariant(*f))]
    #[requires(f.invariant())]
    #[requires(0 <= @i && @i < (@f.clauses).len())]
    #[ensures((*self).compatible(^self))]
    #[ensures(f.eventually_sat_complete(*self) === f.eventually_sat_complete(^self))]
    #[ensures((result === ClauseState::Unit)    ==> (@f.clauses)[@i].unit(*self) && !(self).complete())]
    #[ensures((result === ClauseState::Sat)     ==> (@f.clauses)[@i].sat(^self) && @self === @^self)]
    #[ensures((result === ClauseState::Unsat)   ==> (@f.clauses)[@i].unsat(^self) && @self === @^self)]
    #[ensures((result === ClauseState::Unknown) ==> @self === @^self && !(^self).complete())]
    #[ensures((self).complete() ==> *self === ^self && ((result === ClauseState::Unsat) || (result === ClauseState::Sat)))]
    pub fn unit_prop_once(&mut self, i: usize, f: &Formula) -> ClauseState {
        let clause = &f.clauses[i];
        let old_a = Ghost::record(&self);
        proof_assert!(^self === ^@old_a);
        match clause.check_if_unit(self, f) {
            ClauseState::Unit => {
                // I tried both to make ClauseState::Unit contain a usize and to return a tuple, but
                // both were slower than getting it after. Kind of makes sense since unit clauses are
                // rare and we on average have to traverse n/2 lits to find the unit lit. If I make formula
                // mutable, then I can swap to index 0 and skip the call to clause.get_unit()
                let lit = clause.get_unit(self, f);
                proof_assert!(clause.invariant((@self).len()));
                proof_assert!(lemma_unit_wrong_polarity_unsat_formula(*clause, *f, @self, @lit.idx, bool_to_assignedstate(lit.polarity)); true);
                proof_assert!(forall<j: Int> 0 <= j && j < (@clause).len() && !(@(@clause)[j].idx === @lit.idx) ==> !((@clause)[j].unset(*self)));
                proof_assert!(lemma_unit_forces(*clause, *f, @self, @lit.idx, bool_to_assignedstate(lit.polarity)); true);
                if lit.polarity {
                    self.0[lit.idx] = 1;
                } else {
                    self.0[lit.idx] = 0;
                }
                proof_assert!(lemma_extension_sat_base_sat(*f, @@old_a, @lit.idx, bool_to_assignedstate(lit.polarity)); true);
                proof_assert!(lemma_extensions_unsat_base_unsat(@@old_a, @lit.idx, *f); true);
                proof_assert!(^self === ^@old_a);
                return ClauseState::Unit;
            }
            o => return o,
        }
    }

    #[cfg_attr(feature = "trust_assignments", trusted)]
    #[requires(f.invariant())]
    #[requires(self.invariant(*f))]
    #[ensures((^self).invariant(*f))]
    #[ensures(f.eventually_sat_complete(^self) === f.eventually_sat_complete(*self))]
    #[ensures((*self).compatible(^self))]
    #[ensures(match result { 
        ClauseState::Sat => f.sat(^self),
        ClauseState::Unsat => f.unsat(^self),
        ClauseState::Unknown => !(^self).complete(),
        ClauseState::Unit => !self.complete(),
    })]
    #[ensures((self).complete() ==> *self === (^self) && ((result === ClauseState::Unsat) || f.sat(*self)))]
    pub fn unit_propagate(&mut self, f: &Formula) -> ClauseState {
        let old_a = Ghost::record(&self);
        let mut i: usize = 0;
        let mut out = ClauseState::Sat;
        #[invariant(ai, self.invariant(*f))]
        #[invariant(proph, ^self === ^@old_a)]
        #[invariant(compat, (*@old_a).compatible(*self))]
        #[invariant(maintains_sat, f.eventually_sat_complete(*@old_a) === f.eventually_sat_complete(*self))]
        #[invariant(out_not_unsat, !(out === ClauseState::Unsat))]
        #[invariant(inv, (@old_a).complete() ==> 
            *@old_a === *self && forall<j: Int> 0 <= j && j < @i ==>
             !(@f.clauses)[j].unknown(*self) && !(@f.clauses)[j].unit(*self) && (@f.clauses)[j].sat(*self)
        )]
        #[invariant(inv2,
            out === ClauseState::Sat ==> forall<j: Int> 0 <= j && j < @i ==>
             !(@f.clauses)[j].unsat(*self) && !(@f.clauses)[j].unknown(*self) && !(@f.clauses)[j].unit(*self) && (@f.clauses)[j].sat(*self)
        )]
        #[invariant(inv3,
            out === ClauseState::Unit ==> !(*@old_a).complete() 
            //&& exists<j: Int> 0 <= j && j < @i && (@f.clauses)[j].unit(*@old_a)
        )]
        #[invariant(inv4,
            out === ClauseState::Unknown ==> !self.complete()//exists<j: Int> 0 <= j && j < @i ==>
             //(@f.clauses)[j].unknown(*self)
        )]
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
    #[requires(self.invariant(*f))]
    #[ensures((^self).invariant(*f))]
    #[ensures(f.eventually_sat_complete(*self) === f.eventually_sat_complete(^self))]
    #[ensures((*self).compatible(^self))]
    #[ensures(result === Some(false) ==> f.unsat(^self))]
    #[ensures(result === Some(true) ==> f.sat(^self))]
    #[ensures(result === None ==> !(^self).complete())]
    pub fn do_unit_propagation(&mut self, f: &Formula) -> Option<bool> {
        let old_a = Ghost::record(&self);
        #[invariant(ai, self.invariant(*f))]
        #[invariant(proph, ^self === ^@old_a)]
        #[invariant(compat, (*@old_a).compatible(*self))]
        #[invariant(maintains_sat, f.eventually_sat_complete(*@old_a) ==> f.eventually_sat_complete(*self))]
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