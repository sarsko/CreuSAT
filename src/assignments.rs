extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;
use crate::ghost;
use crate::lit::*;
use crate::clause::*;
use crate::logic::*;
use crate::predicates::*;
use crate::formula::*;

pub struct Assignments(pub Vec<AssignedState>);

#[derive(Copy, Eq)]
pub enum AssignedState {
    Unset,
    Positive,
    Negative,
}

#[trusted] // TMP, PASSES
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

// Predicates
impl Assignments { 
    #[predicate]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            @f.num_vars === (@self).len()
        }
    }

    #[predicate]
    pub fn compatible_complete(self, a2: Assignments) -> bool {
        self.compatible(a2) && a2.complete()
    }

    #[predicate]
    pub fn complete(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self).len() ==> !((@self)[i] === AssignedState::Unset)
        }
    }

    #[predicate]
    pub fn compatible(self, a2: Assignments) -> bool {
        pearlite! { compatible_inner(@self, @a2) }
    }
}

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

    #[trusted]
    #[ensures(forall<i: Int> 0 <= i && i < (@self).len() ==> (@self)[i] === (@result)[i])]
    #[ensures((@self).len() === (@result).len())]
    #[ensures(*self === result)]
    pub fn clone(&self) -> Self {
        Assignments(self.clone_assignment_vector(&self.0))
    }

    #[trusted] // TMP, PASSES
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

    #[trusted] // FIX
    #[requires(_f.invariant())]
    #[requires(self.invariant(*_f))]
    #[requires(0 <= @ix && @ix < (@self).len())]
    //#[requires(!(s === AssignedState::Unset))]
    #[requires((@self)[@ix] === AssignedState::Unset)]
    #[ensures((^self).invariant(*_f))]
    #[ensures((*self).compatible(^self))]
    #[ensures(@(^self) === (@self).set(@ix, s))] // This needs to go
    //#[ensures(@(^self) == (@self).set(@ix, s))]
    #[ensures((@^self)[@ix] === s)]
    #[ensures((forall<j : Int> 0 <= j && j < (@self).len() && 
        j != @ix ==> (@*self)[j] === (@^self)[j]))]
    #[ensures((@self).len() === (@^self).len())]
    pub fn assign(&mut self, ix: usize, s: AssignedState, _f: &Formula) {
        self.0[ix] = s;
    }

    #[trusted] // TMP, PASSES
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
    #[ensures(f.eventually_unsat(*self) ==> f.eventually_unsat(^self))] // Checks out
    #[ensures(f.eventually_sat(^self) ==> f.eventually_sat(*self))] // Checks out
    #[ensures(f.eventually_sat(*self) ==> f.eventually_sat(^self))] // TODO
    //#[ensures(f.eventually_unsat(^self) ==> f.eventually_unsat(*self))] // TODO
    pub fn unit_prop_once(&mut self, i: usize, f: &Formula) -> bool {
        let clause = &f.clauses[i];
        let old_a = Ghost::record(&self);

        //proof_assert! {{ lemma_unsat_implies_not_unit(*clause, *self); true}}

        proof_assert! { ^self === ^@old_a }
        if clause.check_if_unit(self, f) {
            let lit = clause.get_unit(self, f);
            let old_a2 = Ghost::record(&self);
            proof_assert! {{ lemma_test(@self, @lit.idx, *f); true}}
            proof_assert! { {lemma_has_to_assign2(@clause, lit, @self, *f); true}}
            proof_assert! { {lemma_has_to_assign3(@clause, lit, @self, *f); true}}
            proof_assert! {!lit_sat(lit, @self)}
            proof_assert! {!clause_sat(@clause, @self)}
            proof_assert! {is_unass_in(@clause, lit, @self)}
            if lit.polarity {
                proof_assert! {{ lemma_test_pos(@self, lit.polarity, @lit.idx, *f); true}}
                self.assign(lit.idx, AssignedState::Positive, f);
                //self.0[lit.idx] = AssignedState::Positive;
                proof_assert! {@self === (@@old_a2).set(@lit.idx, AssignedState::Positive)}
            } else {
                proof_assert! {{ lemma_test_neg(@self, lit.polarity, @lit.idx, *f); true}}
                self.assign(lit.idx, AssignedState::Negative, f);
                //self.0[lit.idx] = AssignedState::Negative;
                proof_assert! {@self === (@@old_a2).set(@lit.idx, AssignedState::Negative)}
            }
            proof_assert! {lit_sat(lit, @self)}
            proof_assert! {clause_sat(@clause, @self)}
            proof_assert! {eventually_sat_formula_inner(@@old_a2, *f) ==> eventually_sat_formula_inner(@self, *f)}
            return true;
        }
        return false;
    }

    #[trusted] // TMP
    #[requires(f.invariant())]
    #[requires(self.invariant(*f))]
    #[ensures((^self).invariant(*f))]
    #[ensures(f.eventually_unsat(*self) === f.eventually_unsat(^self))]
    #[ensures(f.eventually_sat(^self) === f.eventually_sat(*self))]
    #[ensures((*self).compatible(^self))]
    pub fn unit_propagate(&mut self, f: &Formula) -> bool {
        let old_a = Ghost::record(&self);
        let mut i: usize = 0;
        let mut out = false;
        #[invariant(loop_invariant, 0usize <= i && @i <= (@f.clauses).len())]
        #[invariant(ai, self.invariant(*f))]
        #[invariant(proph, ^self === ^@old_a)]
        #[invariant(compat, (*@old_a).compatible(*self))]
        #[invariant(maintains_sat, f.eventually_sat(*@old_a) ==> f.eventually_sat(*self))]
        #[invariant(maintains_unsat2, f.eventually_unsat(*self) ==> f.eventually_unsat(*@old_a))]
        #[invariant(maintains_unsat, f.eventually_unsat(*@old_a) ==> f.eventually_unsat(*self))]
        #[invariant(maintains_sat2, f.eventually_sat(*self) ==> f.eventually_sat(*@old_a))]
        while i < f.clauses.len() {
            if self.unit_prop_once(i, f) {
                out = true;
            }
            i += 1
        }
        return out;
    }

    #[trusted] // TMP
    #[requires(f.invariant())]
    #[requires(self.invariant(*f))]
    #[ensures((^self).invariant(*f))]
    #[ensures(f.eventually_sat(*self) === f.eventually_sat(^self))] // OK for Inner
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

#[logic]
#[requires(0 <= @l.idx && @l.idx < a.len())]
#[requires(a[@l.idx] === AssignedState::Unset)]
#[requires(eventually_sat_formula_inner(a, f))]
#[requires(l.polarity)]
#[requires(!lit_sat(l, a))]
#[requires(unit_internal(c, a))]
#[requires(is_unass_in(c, l, a))]
#[ensures(eventually_sat_formula_inner(a.set(@l.idx, AssignedState::Positive), f))]
fn lemma_has_to_assign2(c: Seq<Lit>, l: Lit, a: Seq<AssignedState>, f: Formula) {
    pearlite! {
        compatible_inner(a, a.set(@l.idx, AssignedState::Positive)) &&
        compatible_inner(a, a.set(@l.idx, AssignedState::Negative)) 
    };
}

#[logic]
#[requires(0 <= @l.idx && @l.idx < a.len())]
#[requires(a[@l.idx] === AssignedState::Unset)]
#[requires(eventually_sat_formula_inner(a, f))]
#[requires(!l.polarity)]
#[requires(!lit_sat(l, a))]
#[requires(unit_internal(c, a))]
#[requires(is_unass_in(c, l, a))]
#[ensures(eventually_sat_formula_inner(a.set(@l.idx, AssignedState::Negative), f))]
fn lemma_has_to_assign3(c: Seq<Lit>, l: Lit, a: Seq<AssignedState>, f: Formula) {
    pearlite! {
        compatible_inner(a, a.set(@l.idx, AssignedState::Positive)) &&
        compatible_inner(a, a.set(@l.idx, AssignedState::Negative)) 
    };
}

#[logic]
#[requires(0 <= ix && ix < a.len())]
#[requires(a[ix] === AssignedState::Unset)]
#[requires(formula_sat(f, a))]
#[ensures(formula_sat(f, a.set(ix, AssignedState::Positive)))]
#[ensures(formula_sat(f, a.set(ix, AssignedState::Negative)))]
fn lemma_test(a: Seq<AssignedState>, ix: Int, f: Formula) {}

#[logic]
#[requires(0 <= ix && ix < a.len())]
#[requires(a[ix] === AssignedState::Unset)]
#[requires(clause_sat(c, a))]
#[ensures(clause_sat(c, a.set(ix, AssignedState::Positive)))]
#[ensures(clause_sat(c, a.set(ix, AssignedState::Negative)))]
fn lemma_clause(a: Seq<AssignedState>, ix: Int, c: Seq<Lit>) {}

#[logic]
#[requires(0 <= ix && ix < a.len())]
#[requires(a[ix] === AssignedState::Unset)]
#[requires(eventually_sat_formula_inner(a, f))]
#[requires(polarity)]
#[ensures(eventually_sat_formula_inner(a.set(ix, AssignedState::Positive), f))]
fn lemma_test_neg(a: Seq<AssignedState>, polarity: bool, ix: Int, f: Formula) {}

#[logic]
#[requires(0 <= ix && ix < a.len())]
#[requires(a[ix] === AssignedState::Unset)]
#[requires(eventually_sat_formula_inner(a, f))]
#[requires(!polarity)]
#[ensures(eventually_sat_formula_inner(a.set(ix, AssignedState::Negative), f))]
fn lemma_test_pos(a: Seq<AssignedState>, polarity: bool, ix: Int, f: Formula) {}