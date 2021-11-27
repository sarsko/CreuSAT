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

    #[requires(_f.invariant())]
    #[requires(self.invariant(*_f))]
    #[requires(0 <= @ix && @ix < (@self).len())]
    #[requires((@self)[@ix] === AssignedState::Unset)]
    #[ensures((^self).invariant(*_f))]
    #[ensures((*self).compatible(^self))]
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
}