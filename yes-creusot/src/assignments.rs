extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::formula::*;
use crate::lit::*;
use crate::trail::*;

//#[derive(Eq, PartialEq)]
pub struct Assignments(pub Vec<Option<bool>>);

impl Model for Assignments {
    type ModelTy = Seq<Option<bool>>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        self.0.model()
    }
}

impl Assignments {
    #[predicate]
    pub fn invariant(self, n: Int) -> bool {
        pearlite! {
            n === (@self).len()
        }
    }
}

impl Assignments {
    /*
    #[allow(dead_code)]
    fn clone_assignment_vector(&self) -> Vec<Option<bool>> {
        let mut out = Vec::new();
        let mut i = 0;
        while i < self.0.len() {
            let curr = self.0[i];
            out.push(creusot_contracts::std::Clone::clone(&curr));
            //out.push(std::clone::Clone::clone(&curr));
            i += 1;
        }
        return out;
    }

    #[allow(dead_code)]
    fn clone(&self) -> Self {
        Assignments(self.clone_assignment_vector())
    }
    */

    #[trusted] // TMP
    #[requires(self.invariant(@_f.num_vars))]
    #[ensures((^self).invariant(@_f.num_vars))]
    //#[requires(self.invariant(n))]
    //#[ensures(self.compatible(^self))]
    //#[ensures((@^self)[@lit.idx] === Some(lit.polarity))]
    //#[ensures((forall<j : Int> 0 <= j && j < (@self).len() && 
    //j != @ix ==> (@*self)[j] === (@^self)[j]))]
    //#[requires((@self)[@lit.idx] === None)] // This is a correctness req
    #[requires(0 <= @lit.idx && @lit.idx < (@self).len())]
    #[ensures((@^self)[@lit.idx] === Some(lit.polarity))]
    #[ensures(@^self == (@*self).set(@lit.idx, Some(lit.polarity)))]
    /*
    #[ensures((*self).compatible(^self))]
    #[ensures((forall<j : Int> 0 <= j && j < (@self).len() && 
        j != @ix ==> (@*self)[j] === (@^self)[j]))]
        */
    #[ensures((@^self).len() === (@self).len())]
    pub fn set_assignment(&mut self, lit: Lit, _f: &Formula) {
        /*
        if !self.0[l.idx].is_none() {
            panic!("Assignment already set.");
        }
        */
        self.0[lit.idx] = Some(lit.polarity);
    }

    #[ensures(result.invariant(@f.num_vars))]
    pub fn init_assignments(f: &Formula) -> Assignments {
        let mut assign: Vec<Option<bool>> = Vec::new();
        let mut i: usize = 0;
        #[invariant(len_correct, (@assign).len() === @i)]
        #[invariant(i_less, @i <= @f.num_vars)]
        while i < f.num_vars {
            assign.push(None);
            i += 1
        }
        Assignments(assign)
    }

    #[trusted] // TMP
    #[ensures(match result {
        Some(lit) => (@self)[@lit.idx] === None,
        None => forall<i : Int> 0 <= i && i < (@self).len() ==> 
                !((@self)[i] === None)
    })]
    #[ensures(match result {
        Some(lit) => 0 <= @lit.idx && @lit.idx < (@self).len(),
        None => true
    })]
    pub fn find_unassigned_lit(&self) -> Option<Lit> {
        let mut i: usize = 0;
        #[invariant(i_less, 0 <= @i && @i <= (@self).len())]
        #[invariant(all_set, forall<j : Int> 0 <= j && j < @i ==> 
            !((@self)[j] === None))]
        while i < self.0.len() {
            let curr = self.0[i];
            match curr {
                Some(_) => {} // continue
                None => {
                    return Some(Lit{ idx: i, polarity: true });
                }
            }
            i += 1;
        }
        None
    }   

    #[trusted] // TMP
    #[requires(@level <= (@trail.trail).len())]
    #[requires(trail.invariant(*_f))]
    #[requires(self.invariant(@_f.num_vars))]
    #[ensures((^trail).invariant(*_f))]
    #[ensures((^self).invariant(@_f.num_vars))]
    #[ensures((@(^trail).vardata).len() === (@trail.vardata).len())]
    #[ensures((@(^trail).trail).len() === @level)]
    #[ensures(forall<j: Int> 0 <= j && j < @level ==> 
        (@(^trail).trail)[j] === (@trail.trail)[j])] // new
    pub fn cancel_until(&mut self, trail: &mut Trail, level: usize, _f: &Formula) {
        let mut i: usize = trail.trail.len();
        let old_self = Ghost::record(&self);
        let old_trail = Ghost::record(&trail);
        #[invariant(i_is_trail_len, @i === (@trail.trail).len())]
        #[invariant(maintains_trail_inv, trail.invariant(*_f))]
        #[invariant(maintains_ass_inv, self.invariant((@trail.vardata).len()))]
        #[invariant(intact, ^self === ^@old_self)]
        #[invariant(intact_trail, ^trail === ^@old_trail)]
        while i > level {
            let decisions = trail.trail.pop();
            match decisions {
                Some(decisions) => {
                    let mut j: usize = 0;
                    #[invariant(maintains_trail_inv2, trail.invariant(*_f))]
                    #[invariant(maintains_ass_inv2, self.invariant((@trail.vardata).len()))]
                    #[invariant(same_len_trail, (@trail.vardata).len() === (@(@old_trail).vardata).len())]
                    #[invariant(intact_self2, ^self === ^@old_self)]
                    #[invariant(intact_trail2, ^trail === ^@old_trail)]
                    #[invariant(i_is_trail_len2, @i - 1 === (@trail.trail).len())]
                    while j < decisions.len() {
                        let lit = decisions[j];
                        proof_assert! { (@trail.vardata).len() > @lit.idx };
                        trail.vardata[lit.idx] = (0, Reason::Undefined); // Comment out this to make it pass
                        //self.0[lit.idx] = None;
                        j += 1;
                    }
                }
                None => {
                    panic!("Trail is empty.");
                }
            }
            i -= 1;
        }
    }
}