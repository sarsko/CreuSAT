extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::lit::*;
use crate::clause::*;
use crate::logic::*;
use crate::formula::*;

pub struct Assignments(pub Vec<AssignedState>);

//#[derive(Copy, Eq)]
pub enum AssignedState {
    Unset,
    Positive,
    Negative,
}


impl PartialEq for AssignedState {
    fn eq(&self, other: &Self) -> bool {
        return match (self, other) {
            (AssignedState::Unset, AssignedState::Unset) => true,
            (AssignedState::Positive, AssignedState::Positive) => true,
            (AssignedState::Negative, AssignedState::Negative) => true,
            _ => false,
        };
    }
}

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
            @f.num_vars === (@self).len()
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
    #[trusted]
    #[ensures(forall<i: Int> 0 <= i && i < (@self).len() ==> (@self)[i] === (@result)[i])]
    #[ensures((@self).len() === (@result).len())]
    #[ensures(@*self == @result)]
    pub fn clone(&self) -> Self {
        let mut out = Vec::new();
        let mut i: usize = 0;
        #[invariant(loop_invariant, 0 <= @i && @i <= (@self).len())]
        #[invariant(equality, forall<j: Int> 0 <= j && j < @i ==> (@out)[j] === (@self)[j])]
        #[invariant(len, (@out).len() === @i)]
        while i < self.0.len() {
            //let curr = self.0[i];
            //out.push(curr.clone());
            i += 1;
        }
        Assignments(out)
    }

    #[requires(f.invariant())]
    #[ensures(result.invariant(*f))]
    pub fn new(f: &Formula) -> Self {
        //Assignments(vec::from_elem(AssignedState::Unset, f.num_vars))
        let mut assign: Vec<AssignedState> = Vec::new();
        let mut i: usize = 0;
        #[invariant(loop_invariant, 0 <= @i && @i <= @f.num_vars)]
        #[invariant(length_invariant, (@assign).len() === @i)]
        while i < f.num_vars {
            assign.push(AssignedState::Unset);
            i += 1
        }
        Assignments(assign)
    }

    #[requires(!self.complete())]
    #[ensures(@result < (@self).len())]
    #[ensures((@self)[@result] === AssignedState::Unset)]
    pub fn find_unassigned(&self) -> usize {
        let mut i: usize = 0;
        #[invariant(prev, forall<j: Int> 0 <= j && j < @i ==> !((@self)[j] === AssignedState::Unset))]
        while i < self.0.len() {
            let curr = &self.0[i];
            match curr {
                AssignedState::Unset => {
                    return i;
                },
                _ => {},
            }
            i += 1;
        }
        unreachable!()
    }

    #[requires(f.invariant())]
    #[requires(self.invariant(*f))]
    #[requires(0 <= @i && @i < (@f.clauses).len())]
    #[ensures((^self).invariant(*f))]
    #[ensures((*self).compatible(^self))]
    #[ensures(f.eventually_sat_complete(*self) === f.eventually_sat_complete(^self))] 
    pub fn unit_prop_once(&mut self, i: usize, f: &Formula) -> bool {
        let clause = &f.clauses[i];
        let old_a = Ghost::record(&self);
        proof_assert!(^self === ^@old_a);
        if clause.check_if_unit(self, f) {
            let lit = clause.get_unit(self, f);
            proof_assert!(forall<j: Int> 0 <= j && j < (@clause).len() ==> 0 <= @(@clause)[j].idx && @(@clause)[j].idx < (@self).len());
            proof_assert!(lemma_unitClauseLiteralFalse_tauNotSatisfiable(*clause, *f, @self, @lit.idx, bool_to_assignedstate(lit.polarity)); true);
            proof_assert!(forall<j: Int> 0 <= j && j < (@clause).len() && !(@(@clause)[j].idx === @lit.idx) ==> !((@self)[@(@clause)[j].idx] === AssignedState::Unset));
            proof_assert!(forall<j: Int, k: Int> 0 <= j && j < (@clause).len() && k < j ==> !(@(@clause)[k].idx === @(@clause)[j].idx));
            proof_assert!(lemma_unit_forces(*clause, *f, @self, @lit.idx, bool_to_assignedstate(lit.polarity)); true);
            if lit.polarity {
                self.0[lit.idx] = AssignedState::Positive;
            } else {
                self.0[lit.idx] = AssignedState::Negative;
            }
            proof_assert!(@^self == (@*@old_a).set(@lit.idx, bool_to_assignedstate(lit.polarity)));
            proof_assert!(lemma_extensionSat_baseSat(*f, @@old_a, @lit.idx, bool_to_assignedstate(lit.polarity)); true);
            proof_assert!(lemma_extensionsUnsat_baseUnsat(@@old_a, @lit.idx, *f); true);
            proof_assert!(^self === ^@old_a);
            return true;
        }
        return false;
    }

    #[requires(f.invariant())]
    #[requires(self.invariant(*f))]
    #[ensures((^self).invariant(*f))]
    #[ensures(f.eventually_sat_complete(^self) === f.eventually_sat_complete(*self))]
    #[ensures((*self).compatible(^self))]
    pub fn unit_propagate(&mut self, f: &Formula) -> bool {
        let old_a = Ghost::record(&self);
        let mut i: usize = 0;
        let mut out = false;
        #[invariant(ai, self.invariant(*f))]
        #[invariant(proph, ^self === ^@old_a)]
        #[invariant(compat, (*@old_a).compatible(*self))]
        #[invariant(maintains_sat, f.eventually_sat_complete(*@old_a) === f.eventually_sat_complete(*self))]
        while i < f.clauses.len() {
            if self.unit_prop_once(i, f) {
                out = true;
            }
            i += 1
        }
        return out;
    }

    #[requires(f.invariant())]
    #[requires(self.invariant(*f))]
    #[ensures((^self).invariant(*f))]
    #[ensures(f.eventually_sat_complete(*self) === f.eventually_sat_complete(^self))]
    #[ensures((*self).compatible(^self))]
    pub fn do_unit_propagation(&mut self, f: &Formula) {
        let old_a = Ghost::record(&self);
        #[invariant(ai, self.invariant(*f))]
        #[invariant(proph, ^self === ^@old_a)]
        #[invariant(compat, (*@old_a).compatible(*self))]
        #[invariant(maintains_sat, f.eventually_sat_complete(*@old_a) ==> f.eventually_sat_complete(*self))]
        while self.unit_propagate(f) {}
    }
}