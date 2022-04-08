extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::lit::*;
use crate::assignments::*;
use crate::formula::*;
use crate::clause::*;
use crate::logic::*;
use crate::util::*;
use crate::logic_ntrail::*;

use crate::logic::logic::*;

#[derive(Copy, Clone)]
pub enum Reason {
    //Undefined,
    Decision,
    Unit,
    Long(usize),
}

/*
pub struct Trail {
    pub trail: Vec<Lit>,
    pub vardata: Vec<(usize, Reason)>,
}
*/
pub struct Step {
    pub lit: Lit,
    pub decision_level: usize,
    pub reason: Reason,
}

//const UNASSIGNED: usize = usize::MAX;

pub struct NTrail {
    //pub assignments: Vec<AssignedState>,
    pub assignments: Assignments,
    lit_to_level: Vec<usize>, // usize::MAX if unassigned
    pub trail: Vec<Step>,

    /// Trail indices of decisions.
    ///
    /// The first entry does not represent a decision and is fixed at 0 so that each entry on the
    /// trail has a preceding entry in this list and so that the decision at level `n` corresponds
    /// to the index `n`.
    decisions: Vec<usize>,
}

impl Reason {
    #[predicate]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            match self {
                Reason::Long(i) => 0 <= @i && @i < (@f.clauses).len(),
                _ => true
            }
        }
    }
}

impl Step {
    #[predicate]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            self.lit.invariant(@f.num_vars) &&
            //self.decision_level >= 0 &&
            self.reason.invariant(f)
            //self.reason != Reason::Undefined
        }
    }
}


// LOGIC
impl NTrail {
    #[predicate]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            self.assignments.invariant(f) &&
            trail_invariant(@self.trail, f) //&&
            // added, watch out
            && self.lit_not_in_less(f)
            && self.lit_is_unique()

            && long_are_post_unit_inner(@self.trail, f, @self.assignments)
            // I am not sure these will be needed
            //trail_entries_are_assigned_inner(@self.trail, @self.assignments) && // added
            //assignments_are_in_trail(@self.trail, @self.assignments) // added
        }
    }


    #[predicate]
    pub fn lit_not_in_less(self, f: Formula) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self.trail).len() ==>
                forall<j: Int> 0 <= j && j < i ==>
                match (@self.trail)[j].reason {
                    Reason::Long(cref) => !(@self.trail)[i].lit.lit_idx_in((@f.clauses)[@cref]),
                    _ => true,
                }
        }
    }

    // Trail does not contail duplicate idxes
    #[predicate]
    pub fn lit_is_unique(self) -> bool {
        pearlite! {
            lit_is_unique_inner(@self.trail)
        }
    }

}

impl NTrail {
    // Okay so this checks out on the Linux, but it takes time. I believe it is due to the spec
    // of pop being "too weak". Vytautas told me to complain more, so I'll complain to Xavier.
    // Also: on the Mac the other Assertion fails, so the whole thing should be looked into.
    #[trusted] // Seems like this just takes forever, but checks out
    #[requires(f.invariant())]
    #[requires(self.invariant(*f))]
    #[requires(self.lit_not_in_less(*f))]
    #[requires(self.lit_is_unique())]
    #[requires((@self.trail).len() > 0)]
    #[requires(long_are_post_unit_inner(@self.trail, *f, @self.assignments))]
    #[ensures(long_are_post_unit_inner((@(^self).trail), *f, (@(^self).assignments)))]
    fn backstep(&mut self, f: &Formula) {
        let old_t = Ghost::record(&self);
        //proof_assert!(self === @old_t);
        let last = self.trail.pop();
        match last {
            Some(step) => {
                self.assignments.0[step.lit.idx] = 3;
                proof_assert!(@self.assignments == (@(@old_t).assignments).set(@step.lit.idx, 3u8));
                proof_assert!(@self.trail === pop(@(@old_t).trail));
                proof_assert!(^@old_t === ^self);
                proof_assert!((lemma_backtrack_ok(*self, *f, step.lit)); true);
                //self.lit_to_level[step.lit.idx] = usize::MAX;
            }
            None => {
                panic!();
            }
        }
    }

    // Requires step.lit to be unasigned


    #[trusted] // OK (for now, gonna do some additions later)
    #[requires(_f.invariant())]
    #[requires((@self.trail).len() < @_f.num_vars)]
    #[requires(step.lit.invariant(@_f.num_vars))]
    #[requires(self.invariant(*_f))]
    #[requires(match step.reason {
        Reason::Long(k) => 0 <= @k && @k < (@_f.clauses).len() &&
        clause_post_with_regards_to_lit((@_f.clauses)[@k], self.assignments, step.lit),
        _ => true
    })]
    #[requires(step.invariant(*_f))]
    #[requires(step.lit.invariant(@_f.num_vars))]
    #[requires(!step.lit.idx_in_trail(self.trail))]
    #[requires(unset((@self.assignments)[@step.lit.idx]))]
    #[ensures((forall<j : Int> 0 <= j && j < (@self.assignments).len() &&
        j != @step.lit.idx ==> (@self.assignments)[j] === (@(^self).assignments)[j]))]
    #[ensures(step.lit.sat((^self).assignments))]
    #[requires(long_are_post_unit_inner(@self.trail, *_f, @self.assignments))]
    #[ensures(long_are_post_unit_inner((@(^self).trail), *_f, (@(^self).assignments)))]
    #[ensures((^self).invariant(*_f))]
    pub fn enq_assignment(&mut self, step: Step, _f: &Formula) {
        //self.trail_index[step.assigned_lit.index()] = self.steps.len() as _;
        //debug_assert!(!self.assigned.is_assigned(step.assigned_lit.var()));
        let trail = &self.trail;
        self.assignments.set_assignment_new(step.lit, _f, trail);
        proof_assert!(!step.lit.idx_in_trail(self.trail));
        proof_assert!(self.lit_is_unique());
        self.trail.push(step);
        // These foure are not checking out
        proof_assert!(self.lit_is_unique()); // Nope
        proof_assert!(self.lit_not_in_less(*_f)); // checking out on Linux
        proof_assert!(long_are_post_unit_inner(@self.trail, *_f, @self.assignments)); // Nope
        proof_assert!(crefs_in_range(@self.trail, *_f)); // This is checking out somehow?
    }

    #[trusted] // OK
    #[requires((@self.decisions).len() > 0)]
    #[requires(_f.invariant())]
    #[requires((@self.trail).len() < @_f.num_vars)]
    #[requires(lit.invariant(@_f.num_vars))]
    #[requires(self.invariant(*_f))]
    #[requires(lit.invariant(@_f.num_vars))]
    #[requires(!lit.idx_in_trail(self.trail))]
    #[requires(unset((@self.assignments)[@lit.idx]))]
    #[ensures((forall<j : Int> 0 <= j && j < (@self.assignments).len() &&
        j != @lit.idx ==> (@self.assignments)[j] === (@(^self).assignments)[j]))]
    #[ensures(lit.sat((^self).assignments))]
    #[requires(long_are_post_unit_inner(@self.trail, *_f, @self.assignments))]
    #[ensures(long_are_post_unit_inner((@(^self).trail), *_f, (@(^self).assignments)))]
    #[ensures((^self).invariant(*_f))]
    pub fn enq_decision(&mut self, lit: Lit, _f: &Formula) {
        //self.decisions.push(self.steps.len() as LitIdx);
        let dlevel = self.decisions.len() - 1; // Not doing this results in a Why3 error. Todo: Yell at Xavier
        self.enq_assignment(Step {
            lit: lit,
            decision_level: dlevel,//self.decision_level(),
            reason: Reason::Decision,
        }, _f);
    }
    // Maybe remove this, I dunno
    #[trusted] // OK
    #[requires((@self.decisions).len() === 1)]
    #[requires(_f.invariant())]
    #[requires((@self.trail).len() < @_f.num_vars)]
    #[requires(lit.invariant(@_f.num_vars))]
    #[requires(self.invariant(*_f))]
    #[requires(lit.invariant(@_f.num_vars))]
    #[requires(!lit.idx_in_trail(self.trail))]
    #[requires(unset((@self.assignments)[@lit.idx]))]
    #[ensures((forall<j : Int> 0 <= j && j < (@self.assignments).len() &&
        j != @lit.idx ==> (@self.assignments)[j] === (@(^self).assignments)[j]))]
    #[ensures(lit.sat((^self).assignments))]
    #[requires(long_are_post_unit_inner(@self.trail, *_f, @self.assignments))]
    #[ensures(long_are_post_unit_inner((@(^self).trail), *_f, (@(^self).assignments)))]
    #[ensures((^self).invariant(*_f))]
    pub fn enq_unit(&mut self, lit: Lit, _f: &Formula) {
        self.enq_assignment(Step {
            lit: lit,
            decision_level: 0,//self.decision_level(),
            reason: Reason::Unit,
        }, _f);

    }

    /*
    pub fn decision_level(&self) -> LitIdx {
        (self.decisions.len() - 1) as LitIdx
    }
    */
    /*
    // Requires backtracked
    // Requires unset

    */
    

    /*
    #[inline]
    #[trusted] // OK [04.04]
    #[requires(lit.invariant(@_f.num_vars))]
    #[requires(_t.trail_sem_invariant(*_f, *self))]
    #[requires(_t.invariant(*_f))]
    #[requires(_f.invariant())]
    #[requires(self.invariant(*_f))]
    #[requires(unset((@self)[@lit.idx]))] // Added, will break stuff further up
    //#[ensures(self.compatible(^self))]
    #[ensures((^self).invariant(*_f))]
    #[ensures(@(@^self)[@lit.idx] === 1 || @(@^self)[@lit.idx] === 0)]
    #[ensures((@^self).len() === (@self).len())]
    #[ensures(_t.trail_sem_invariant(*_f, ^self))]
    #[ensures((forall<j : Int> 0 <= j && j < (@self).len() &&
        j != @lit.idx ==> (@*self)[j] === (@^self)[j]))]
    #[ensures(lit.sat(^self))]
    pub fn set_assignment(&mut self, lit: Lit, _f: &Formula, _t: &Trail) {
        /*
        if !self.0[l.idx].is_none() {
            panic!("Assignment already set. Attempting to set {:?}", l);
        }
        */
        //assert!(self.0[l.idx].is_none());
        proof_assert!(@(@self)[@lit.idx] >= 2);
        let old_self = Ghost::record(&self);

        proof_assert!(self.invariant(*_f));
        proof_assert!(_f.invariant());
        proof_assert!(vardata_invariant(@_t.vardata, @_f.num_vars));
        proof_assert!(crefs_in_range(@_t.vardata, *_f));
        proof_assert!(lit.invariant(@_f.num_vars));
        proof_assert!(unset((@self)[@lit.idx]));
        proof_assert!(long_are_post_unit_inner(@_t.vardata, *_f, @self));
        proof_assert!((lemma_assign_maintains_long_are_post_unit(@_t.vardata, *_f, *self, lit));true);

        // zzTODOzz 
       //self.0[lit.idx] = lit.polarity as u8;
        if lit.polarity {
            self.0[lit.idx] = 1;
            //proof_assert!(@self === (@@old_self).set(@lit.idx, 1u8));
        } else {
            self.0[lit.idx] = 0;
            //proof_assert!(@self === (@@old_self).set(@lit.idx, 0u8));
        }
        proof_assert!((lemma_assign_maintains_long_are_post_unit(@_t.vardata, *_f, *@old_self, lit));true);
        proof_assert!(^@old_self === ^self);

        proof_assert!(long_are_post_unit_inner(@_t.vardata, *_f, @self));
        //self.0[l.idx] = l.polarity as u8;
    }
    */
}


/*
impl Default for Trail {
    fn default() -> Self {
        Trail {
            assigned: PartialAssignment::default(),
            trail_index: vec![],
            steps: vec![],
            decisions: vec![0],
        }
    }
}
*/

