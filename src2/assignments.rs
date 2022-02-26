extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;
use crate::lit::*;
use crate::clause::*;
use crate::logic::*;
use crate::formula::*;

pub struct Assignments(pub Vec<u8>);

pub enum AssignedState {
    Unset,
    Negative,
    Positive,
}

impl Model for Assignments {
    type ModelTy = Seq<u8>;

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
pub fn compatible_inner(a: Seq<u8>, a2: Seq<u8>) -> bool {
    pearlite! {
        a.len() === a2.len() &&
        (forall<i: Int> 0 <= i && i < a.len() ==>
        ((@a[i] >= 2) || a[i] === a2[i]))
    }
}

#[predicate]
pub fn complete_inner(a: Seq<u8>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < a.len() ==> @a[i] < 2
    }
}

#[predicate]
pub fn compatible_complete_inner(a: Seq<u8>, a2: Seq<u8>) -> bool {
    pearlite! {
        compatible_inner(a, a2) && complete_inner(a2)
        /*
        a.len() === a2.len() &&
        (forall<i: Int> 0 <= i && i < a.len() ==>
        ((a[i] === AssignedState::Unset) || a[i] === a2[i]) && !((a2)[i] === AssignedState::Unset))
        */
    }
}

#[predicate]
pub fn assignments_invariant(a: Seq<u8>, f: Formula) -> bool {
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
            forall<i: Int> 0 <= i && i < (@self).len() ==> @(@self)[i] < 2
        }
    }

    #[predicate]
    pub fn compatible_complete(self, a2: Assignments) -> bool {
        self.compatible(a2) && a2.complete()
    }
}

#[logic]
fn flip_v(v: u8) -> u8 {
    if pearlite!{ @v === 0 } {
        1u8
    } else if pearlite!{ @v === 1 } {
        0u8
    } else {
        v
    }
}

#[logic] 
#[requires(f.invariant())]
#[requires(assignments_invariant(a, f))]
#[requires(f.unsat_u8(a))]
#[ensures(!f.eventually_sat_complete_formula_u8(a))]
fn lemma_not_sat_formula_implies_unsat_formula(f: Formula, a: Seq<u8>) {}

#[logic]
#[requires(c.unsat_u8(a))]
#[requires(clause_in_formula(c, f))]
#[ensures(f.unsat_u8(a))]
fn lemma_not_sat_clause_implies_unsat_formula(f: Formula, c: Clause, a: Seq<u8>) {}


#[logic]
#[requires(f.invariant())]
#[requires(@f.num_vars === a.len())]
#[requires(0 <= ix && ix < a.len() && @a[ix] >= 2)]
#[requires(@v < 2)]
#[requires(f.eventually_sat_complete_formula_u8(a))]
#[requires(!f.eventually_sat_complete_formula_u8(a.set(ix, flip_v(v))))]
#[ensures(f.eventually_sat_complete_formula_u8(a.set(ix, v)))]
fn lemma_unit_forces(c: Clause, f: Formula, a: Seq<u8>, ix: Int, v: u8) {
    lemma_not_sat_formula_implies_unsat_formula(f, a);
}

#[logic]
#[requires(f.invariant())]
#[requires(@f.num_vars === a.len())]
#[requires(0 <= ix && ix < a.len() && @a[ix] >= 2)]
#[requires(@v < 2)]
#[requires(c.unit_u8(a))]
#[requires(clause_in_formula(c, f))]
#[requires(forall<j: Int> 0 <= j && j < (@c).len() ==> 0 <= @(@c)[j].idx && @(@c)[j].idx < a.len())]
#[requires(exists<j: Int> 0 <= j && j < (@c).len() && @(@c)[j].idx === ix && bool_to_u8(((@c)[j].polarity)) === v)]
#[requires(forall<j: Int> 0 <= j && j < (@c).len() && !(@(@c)[j].idx === ix) ==> @a[@(@c)[j].idx] < 2)]
//#[requires(forall<j: Int, k: Int> 0 <= j && j < (@c).len() && k < j ==> !(@(@c)[k].idx === @(@c)[j].idx))] // remove?
//#[requires(forall<j: Int> 0 <= j && j < (@c).len() && !(@(@c)[j].idx === ix) ==> !(a[@(@c)[j].idx] === bool_to_assignedstate((@c)[j].polarity)))]
#[requires(forall<j: Int> 0 <= j && j < (@c).len() && !(@(@c)[j].idx === ix) ==> !(@c)[j].sat_u8(a))]
#[ensures(!f.eventually_sat_complete_formula_u8(a.set(ix, flip_v(v))))]
//#[ensures(not_sat_formula_inner(a.set(ix, flip_v(v)), f))]
#[ensures(f.unsat_u8(a.set(ix, flip_v(v))))]
fn lemma_unitClauseLiteralFalse_tauNotSatisfiable(c: Clause, f: Formula, a: Seq<u8>, ix: Int, v: u8) {
    lemma_not_sat_formula_implies_unsat_formula(f, a);
    lemma_correctPolarityMakesClauseSat(c, a, ix, v);
    lemma_incorrectPolarityMakesClauseUnsat(c, a, ix, v);
    lemma_not_sat_clause_implies_unsat_formula(f, c, a.set(ix, flip_v(v)));
}

#[logic]
#[requires(0 <= ix && ix < a.len())]
#[requires(exists<j: Int> 0 <= j && j < (@c).len() && @(@c)[j].idx === ix && bool_to_u8((@c)[j].polarity) === v)]
#[ensures(c.sat_u8(a.set(ix, v)))]
fn lemma_correctPolarityMakesClauseSat(c: Clause, a: Seq<u8>, ix: Int, v: u8) {}

#[logic]
#[requires(0 <= ix && ix < a.len() && @a[ix] >= 2)]
#[requires(c.unit_u8(a))]
//#[requires(!c.sat_u8(a))]
#[requires(@v < 2)] 
#[requires(exists<j: Int> 0 <= j && j < (@c).len() && @(@c)[j].idx === ix && bool_to_u8((@c)[j].polarity) === v)]
#[requires(forall<j: Int> 0 <= j && j < (@c).len() ==> 0 <= @(@c)[j].idx && @(@c)[j].idx < a.len())]
//#[requires(forall<j: Int, k: Int> 0 <= j && j < (@c).len() && k < j ==> !(@(@c)[k].idx === @(@c)[j].idx))]
#[requires(forall<j: Int> 0 <= j && j < (@c).len() && !(@(@c)[j].idx === ix) ==> !(@c)[j].unset_u8(a))]
#[requires(forall<j: Int> 0 <= j && j < (@c).len() && !(@(@c)[j].idx === ix) ==> !(a[@(@c)[j].idx] === bool_to_u8((@c)[j].polarity)))]
#[ensures(forall<j: Int> 0 <= j && j < (@c).len()  ==> (@(a.set(ix, v))[@(@c)[j].idx] < 2))]
#[ensures(@a.set(ix, flip_v(v))[ix] < 2)]
//#[ensures(not_sat_clause_inner(a.set(ix, flip_v(v)), c))]
#[ensures(c.unsat_u8(a.set(ix, flip_v(v))))]
#[ensures(!c.sat_u8(a.set(ix, flip_v(v))))]
fn lemma_incorrectPolarityMakesClauseUnsat(c: Clause, a: Seq<u8>, ix: Int, v: u8) {}

#[logic]
#[requires(0 <= ix && ix < a.len() && @a[ix] >= 2)]
#[requires(f.eventually_sat_complete_formula_u8(a.set(ix, v)))]
#[ensures(f.eventually_sat_complete_formula_u8(a))]
fn lemma_extensionSat_baseSat(f: Formula, a: Seq<u8>, ix: Int, v: u8) {}

#[logic]
#[requires(0 <= ix && ix < a.len() && @a[ix] >= 2)]
#[requires(!f.eventually_sat_complete_formula_u8(a.set(ix, 0u8)))]
#[requires(!f.eventually_sat_complete_formula_u8(a.set(ix, 1u8)))]
#[ensures(!f.eventually_sat_complete_formula_u8(a))]
fn lemma_extensionsUnsat_baseUnsat(a: Seq<u8>, ix: Int, f: Formula) {
    compatible_inner(a, a.set(ix, 1u8));
    compatible_inner(a, a.set(ix, 0u8));
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
        let mut assign: Vec<u8> = Vec::new();
        let mut i: usize = 0;
        #[invariant(loop_invariant, 0 <= @i && @i <= @f.num_vars)]
        #[invariant(length_invariant, (@assign).len() === @i)]
        while i < f.num_vars {
            assign.push(2);
            i += 1
        }
        Assignments(assign)
    }

    #[requires(!self.complete())]
    #[ensures(@result < (@self).len())]
    #[ensures(@(@self)[@result] >= 2)]
    pub fn find_unassigned(&self) -> usize {
        let mut i: usize = 0;
        #[invariant(loop_invariant, 0 <= @i && @i <= (@self).len())]
        #[invariant(prev, forall<j: Int> 0 <= j && j < @i ==>
            @(@self)[j] < 2
        )]
        while i < self.0.len() {
            let curr = self.0[i];
            if curr >= 2 {
                return i;
            }
            i += 1;
        }
        unreachable!()
    }
    #[trusted] // TODO: REMOVE!! NOT GOOD !! BECAUSE OF THE .set ensures
    #[requires(_f.invariant())]
    #[requires(self.invariant(*_f))]
    #[requires(0 <= @ix && @ix < (@self).len())]
    #[requires(@(@self)[@ix] >= 2)]
    #[ensures((^self).invariant(*_f))]
    #[ensures((*self).compatible(^self))]
    #[ensures(@^self === (@*self).set(@ix, s))]
    #[ensures((@^self)[@ix] === s)]
    #[ensures((forall<j : Int> 0 <= j && j < (@self).len() && 
        j != @ix ==> (@*self)[j] === (@^self)[j]))]
    pub fn assign(&mut self, ix: usize, s: u8, _f: &Formula) {
        self.0[ix] = s;
    }

    #[requires(f.invariant())]
    #[requires(self.invariant(*f))]
    #[requires(0 <= @i && @i < (@f.clauses).len())]
    #[ensures((^self).invariant(*f))]
    #[ensures((*self).compatible(^self))]
    #[ensures(f.eventually_sat_complete(*self) ==> f.eventually_sat_complete(^self))] 
    pub fn unit_prop_once(&mut self, i: usize, f: &Formula) -> bool {
        let clause = &f.clauses[i];
        let old_a = Ghost::record(&self);
        proof_assert! { ^self === ^@old_a }
        proof_assert! { f.sat_u8(@self) ===
            (forall<i: Int> 0 <= i && i < (@((*f).clauses)).len() ==>
            (@((*f).clauses))[i].sat_u8(@self))
        }
        if clause.check_if_unit(self, f) {
            let lit = clause.get_unit(self, f);

            proof_assert!(f.invariant());
            proof_assert!(@f.num_vars === (@self).len());
            proof_assert!(0 <= @lit.idx && @lit.idx < (@self).len() && @(@self)[@lit.idx] >= 2);
            proof_assert!(clause.unit_u8(@self));
            proof_assert!(clause_in_formula(*clause, *f));
            //TODO
            //proof_assert!(exists<j: Int> 0 <= j && j < (@clause).len() && @(@clause)[j].idx === ix && bool_to_u8(((@c)[j].polarity)) === v);
            proof_assert!(forall<j: Int> 0 <= j && j < (@clause).len() && !(@(@clause)[j].idx === @lit.idx) ==> !(@clause)[j].sat_u8(@self));

            //proof_assert!(forall<j: Int> 0 <= j && j < (@clause).len() ==> 0 <= @(@c)[j].idx && @(@c)[j].idx < a.len());
            proof_assert! { (forall<j: Int> 0 <= j && j < (@clause).len() ==> 0 <= @(@clause)[j].idx && @(@clause)[j].idx < (@self).len()) }
            proof_assert! {{lemma_unitClauseLiteralFalse_tauNotSatisfiable(*clause, *f, @self, @lit.idx, bool_to_u8(lit.polarity)); true}}
            //proof_assert!(forall<j: Int> 0 <= j && j < (@c).len() && !(@(@c)[j].idx === ix) ==> @a[@(@c)[j].idx] < 2);
            proof_assert! { (forall<j: Int> 0 <= j && j < (@clause).len() && !(@(@clause)[j].idx === @lit.idx) ==> @(@self)[@(@clause)[j].idx] < 2) } // !.unset()
            proof_assert! { (forall<j: Int, k: Int> 0 <= j && j < (@clause).len() && k < j ==> !(@(@clause)[k].idx === @(@clause)[j].idx)) }
            proof_assert! {{lemma_unit_forces(*clause, *f, @self, @lit.idx, bool_to_u8(lit.polarity)); true}}
            if lit.polarity {
                //self.0[lit.idx] = 1;
                self.assign(lit.idx, 1, f);
            //proof_assert!(@v < 2);
            } else {
                //self.0[lit.idx] = 0;
                self.assign(lit.idx, 0, f);
            }
            //#[requires(f.eventually_sat_complete_formula_u8(a.set(ix, v)))]
            //#[requires(!f.eventually_sat_complete_formula_u8(a.set(ix, 0u8)))]
            //#[requires(!f.eventually_sat_complete_formula_u8(a.set(ix, 1u8)))]
            proof_assert! { @^self == (@*@old_a).set(@lit.idx, bool_to_u8(lit.polarity)) }
            proof_assert! {{ lemma_extensionSat_baseSat(*f, @@old_a, @lit.idx, bool_to_u8(lit.polarity)); true }}
            proof_assert! {{ lemma_extensionsUnsat_baseUnsat(@@old_a, @lit.idx, *f); true }}
            proof_assert! { ^self === ^@old_a }
            proof_assert! (f.eventually_sat_complete_formula_u8(@self));
            return true;
        }
        return false;
    }

    #[trusted] //TMP
    #[requires(f.invariant())]
    #[requires(self.invariant(*f))]
    #[ensures((^self).invariant(*f))]
    #[ensures(f.eventually_sat_complete(^self) === f.eventually_sat_complete(*self))]
    #[ensures((*self).compatible(^self))]
    pub fn unit_propagate(&mut self, f: &Formula) -> bool {
        let old_a = Ghost::record(&self);
        let mut i: usize = 0;
        let mut out = false;
        #[invariant(loop_invariant, 0 <= @i && @i <= (@f.clauses).len())]
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
    #[ensures(f.eventually_sat_complete(*self) === f.eventually_sat_complete(^self))] // OK for Inner
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