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

    #[requires((@self)[@lit.idx] === None)]
    #[requires(0 <= @lit.idx && @lit.idx < (@self).len())]
    #[ensures((@^self)[@lit.idx] === Some(lit.polarity))]
    //#[ensures(@^self === (@*self).set(@lit.idx, Some(lit.polarity)))]
    /*
    #[ensures((*self).compatible(^self))]
    #[ensures((forall<j : Int> 0 <= j && j < (@self).len() && 
        j != @ix ==> (@*self)[j] === (@^self)[j]))]
        */
    pub fn set_assignment(&mut self, lit: Lit) {
        /*
        if !self.0[l.idx].is_none() {
            panic!("Assignment already set.");
        }
        */
        self.0[lit.idx] = Some(lit.polarity);
    }

    pub fn init_assignments(f: &Formula) -> Assignments {
        let mut assign: Vec<Option<bool>> = Vec::new();
        let mut i = 0;
        while i < f.num_vars {
            assign.push(None);
            i += 1
        }
        Assignments(assign)
    }

    pub fn find_unassigned_lit(&self) -> Option<Lit> {
        let mut i = 0;
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

    // Safety passes without split. Should clean up proof
    #[trusted]
    #[requires(trail.invariant((@trail.vardata).len()))]
    #[requires(self.invariant((@trail.vardata).len()))]
    #[ensures(trail.invariant((@trail.vardata).len()))]
    #[ensures((^self).invariant((@trail.vardata).len()))]
    #[ensures((^trail).invariant((@trail.vardata).len()))]
    #[ensures((@(^trail).vardata).len() === (@trail.vardata).len())]
    #[ensures((@(^trail).trail).len() === @level)]
    pub fn cancel_until(&mut self, trail: &mut Trail, level: usize) {
        let mut i: usize = trail.trail.len();
        #[invariant(i_is_trail_len, @i === (@trail.trail).len())]
        #[invariant(maintains_trail_inv, trail.invariant((@trail.vardata).len()))]
        #[invariant(maintains_ass_inv, self.invariant((@trail.vardata).len()))]
        while i > level {
            let decisions = trail.trail.pop();
            match decisions {
                Some(decisions) => {
                    let mut j: usize = 0;
                    #[invariant(maintains_trail_inv2, trail.invariant((@trail.vardata).len()))]
                    #[invariant(maintains_ass_inv2, self.invariant((@trail.vardata).len()))]
                    while j < decisions.len() {
                        let lit = decisions[j];
                        proof_assert! { (@trail.vardata).len() > @lit.idx };
                        trail.vardata[lit.idx] = (0, Reason::Undefined); // Comment out this to make it pass
                        self.0[lit.idx] = None;
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