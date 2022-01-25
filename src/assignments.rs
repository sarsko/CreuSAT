extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;
use crate::ghost;
use crate::lit::*;
use crate::clause::*;
use crate::logic::*;
use crate::formula::*;

pub struct Assignments(pub Vec<AssignedState>);

#[derive(Copy, Eq)]
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
        a.len() === a2.len() &&
        forall<i: Int> 0 <= i && i < a.len() ==>
        (a[i] === AssignedState::Unset) || a[i] === a2[i]
    }
}

#[predicate]
pub fn complete_inner(a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < a.len() ==> !(a[i] === AssignedState::Unset)
    }
}

#[predicate]
pub fn compatible_complete_inner(a: Seq<AssignedState>, a2: Seq<AssignedState>) -> bool {
    pearlite! {
        compatible_inner(a, a2) && complete_inner(a2)
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
            forall<i: Int> 0 <= i && i < (@self).len() ==> !((@self)[i] === AssignedState::Unset)
        }
    }

    #[predicate]
    pub fn compatible_complete(self, a2: Assignments) -> bool {
        self.compatible(a2) && a2.complete()
    }
}

#[logic]
#[ensures(result === !b)]
fn lnot(b: bool) -> bool {
    !b
}

#[logic]
#[requires(!eventually_sat_formula_inner(a, f))]
#[ensures(eventually_unsat_formula_inner(a, f))]
fn lemma_either_or(f: Formula, a: Seq<AssignedState>) {}

#[logic]
#[requires(!eventually_unsat_formula_inner(a, f))]
#[ensures(eventually_sat_formula_inner(a, f))]
fn lemma_either_or2(f: Formula, a: Seq<AssignedState>) {}

#[logic]
#[requires(eventually_unsat_formula_inner(a, f))]
#[ensures(!eventually_sat_formula_inner(a, f))]
fn lemma_either_or3(f: Formula, a: Seq<AssignedState>) {}

#[logic]
#[requires(eventually_sat_formula_inner(a, f))]
#[ensures(!eventually_unsat_formula_inner(a, f))]
fn lemma_either_or4(f: Formula, a: Seq<AssignedState>) {}

#[logic]
fn lemma_mutually_exclusive(f: Formula, a: Seq<AssignedState>) {
    lemma_either_or(f, a);
    lemma_either_or2(f, a);
    lemma_either_or3(f, a);
    lemma_either_or4(f, a);
}

#[logic]
#[requires(f.invariant())]
#[requires(@f.num_vars === a.len())]
#[requires(0 <= i && i < a.len())]
#[requires(a[i] === AssignedState::Unset)]
#[requires(unit_inner(a, c))]
#[requires(exists<j: Int> 0 <= j && j < (@c).len() && @(@c)[j].idx === i && bool_to_assignedstate(lnot((@c)[j].polarity)) === v)]
#[ensures(eventually_unsat_formula_inner(a.set(i, v), f))]
#[ensures(!eventually_sat_formula_inner(a.set(i, v), f))]
#[ensures(not_sat_formula_inner(a.set(i, v), f))]
fn lemma_unitClauseLiteralFalse_tauNotSatisfiable(c: Clause, f: Formula, a: Seq<AssignedState>, i: Int, v: AssignedState) {}

#[logic]
#[requires(f.invariant())]
#[requires(@f.num_vars === a.len())]
#[requires(0 <= i && i < a.len())]
#[requires(a[i] === AssignedState::Unset)]
#[requires(unit_inner(a, c))]
#[requires(exists<j: Int> 0 <= j && j < (@c).len() && @(@c)[j].idx === i && bool_to_assignedstate(((@c)[j].polarity)) === v)]
#[requires(eventually_sat_formula_inner(a, f))]
#[ensures(eventually_sat_formula_inner(a.set(i, v), f))]
fn lemma_unitClauseLiteralTrue_tauSat(c: Clause, f: Formula, a: Seq<AssignedState>, i: Int, v: AssignedState) {}



#[logic]
#[requires(f.invariant())]
#[requires(@f.num_vars === a.len())]
#[requires(0 <= i && i < a.len())]
#[requires(a[i] === AssignedState::Unset)]
#[requires(eventually_sat_formula_inner(a.set(i, v), f))]
#[requires(v === AssignedState::Positive || v === AssignedState::Negative)]
#[ensures(eventually_sat_formula_inner(a, f))]
fn lemma_extensionSat_baseSat(f: Formula, a: Seq<AssignedState>, i: Int, v: AssignedState) {}



impl Assignments {
    #[trusted]
    #[ensures(forall<i: Int> 0 <= i && i < (@v).len() ==> (@v)[i] === (@result)[i])]
    #[ensures((@v).len() === (@result).len())]
    #[ensures(*v === result)]
    pub fn clone_assignment_vector(&self, v: &Vec<AssignedState>) -> Vec<AssignedState> {
        let mut out = Vec::new();
        let mut i: usize = 0;
        #[invariant(loop_invariant, 0 <= @i && @i <= (@v).len())]
        #[invariant(equality, forall<j: Int> 0 <= j && j < @i ==> (@out)[j] === (@v)[j])]
        while i < v.len() {
            let curr = v[i];
            out.push(curr.clone());
            i += 1;
        }
        return out;
    }

    #[ensures(forall<i: Int> 0 <= i && i < (@self).len() ==> (@self)[i] === (@result)[i])]
    #[ensures((@self).len() === (@result).len())]
    #[ensures(*self === result)]
    pub fn clone(&self) -> Self {
        Assignments(self.clone_assignment_vector(&self.0))
    }

    #[requires(f.invariant())]
    #[ensures(result.invariant(*f))]
    pub fn new(f: &Formula) -> Self {
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

    #[trusted] // TODO: REMOVE!! NOT GOOD !! BECAUSE OF THE .set ensures
    #[requires(_f.invariant())]
    #[requires(self.invariant(*_f))]
    #[requires(0 <= @ix && @ix < (@self).len())]
    #[requires((@self)[@ix] === AssignedState::Unset)]
    #[ensures((^self).invariant(*_f))]
    #[ensures((*self).compatible(^self))]
    #[ensures(@^self === (@*self).set(@ix, s))]
    #[ensures((@^self)[@ix] === s)]
    #[ensures((forall<j : Int> 0 <= j && j < (@self).len() && 
        j != @ix ==> (@*self)[j] === (@^self)[j]))]
    pub fn assign(&mut self, ix: usize, s: AssignedState, _f: &Formula) {
        self.0[ix] = s;
    }

    #[requires(!self.complete())]
    #[ensures(@result < (@self).len())]
    #[ensures((@self)[@result] === AssignedState::Unset)]
    pub fn find_unassigned(&self) -> usize {
        let mut i: usize = 0;
        #[invariant(loop_invariant, 0 <= @i && @i <= (@self).len())]
        #[invariant(prev, forall<j: Int> 0 <= j && j < @i ==>
            !((@self)[j] === AssignedState::Unset)
        )]
        while i < self.0.len() {
            let curr = self.0[i];
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
    #[ensures(f.eventually_unsat(*self) === f.eventually_unsat(^self))]
    #[ensures(f.eventually_sat(*self) === f.eventually_sat(^self))] 
    pub fn unit_prop_once(&mut self, i: usize, f: &Formula) -> bool {
        let clause = &f.clauses[i];
        let old_a = Ghost::record(&self);
        proof_assert! { ^self === ^@old_a }
        if clause.check_if_unit(self, f) {
            let lit = clause.get_unit(self, f);
            proof_assert! {{ lemma_mutually_exclusive(*f, @self); true}}
            if lit.polarity {
                proof_assert! {{lemma_unitClauseLiteralTrue_tauSat(*clause, *f, @self, @lit.idx, AssignedState::Positive); true}}
                //self.0[lit.idx] = AssignedState::Positive;
                self.assign(lit.idx, AssignedState::Positive, f);
            } else {
                proof_assert! {{lemma_unitClauseLiteralTrue_tauSat(*clause, *f, @self, @lit.idx, AssignedState::Negative); true}}
                //self.0[lit.idx] = AssignedState::Negative;
                self.assign(lit.idx, AssignedState::Negative, f);
            }
            proof_assert! {{ lemma_extensionSat_baseSat(*f, @@old_a, @lit.idx, bool_to_assignedstate(lit.polarity)); true }}
            proof_assert! { ^self === ^@old_a }
            return true;
        }
        return false;
    }

    #[requires(f.invariant())]
    #[requires(self.invariant(*f))]
    #[ensures((^self).invariant(*f))]
    #[ensures(f.eventually_unsat(*self) === f.eventually_unsat(^self))] // Checks out
    #[ensures(f.eventually_sat(^self) === f.eventually_sat(*self))] // Checks out
    #[ensures((*self).compatible(^self))]
    pub fn unit_propagate(&mut self, f: &Formula) -> bool {
        let old_a = Ghost::record(&self);
        let mut i: usize = 0;
        let mut out = false;
        #[invariant(loop_invariant, 0usize <= i && @i <= (@f.clauses).len())]
        #[invariant(ai, self.invariant(*f))]
        #[invariant(proph, ^self === ^@old_a)]
        #[invariant(compat, (*@old_a).compatible(*self))]
        #[invariant(maintains_sat, f.eventually_sat(*@old_a) === f.eventually_sat(*self))]
        #[invariant(maintains_unsat2, f.eventually_unsat(*self) === f.eventually_unsat(*@old_a))]
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
    #[ensures(f.eventually_sat(*self) ==> f.eventually_sat(^self))] // OK for Inner
    #[ensures(f.eventually_unsat(*self) === f.eventually_unsat(^self))] // Needs ===
    #[ensures((*self).compatible(^self))]
    pub fn do_unit_propagation(&mut self, f: &Formula) {
        let old_a = Ghost::record(&self);
        #[invariant(ai, self.invariant(*f))]
        #[invariant(proph, ^self === ^@old_a)]
        #[invariant(compat, (*@old_a).compatible(*self))]
        #[invariant(maintains_sat, f.eventually_sat(*@old_a) ==> f.eventually_sat(*self))]
        #[invariant(maintains_unsat, f.eventually_unsat(*@old_a) === f.eventually_unsat(*self))]
        while self.unit_propagate(f) {
        }
    }
}