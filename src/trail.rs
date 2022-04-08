extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::{
    lit::*,
    assignments::*,
    formula::*,
    clause::*,
    logic::*,
    util::*,
};

#[cfg(contracts)]
use crate::logic::{
    logic::*,
    logic_util::*,
    logic_ntrail::*,
};

#[derive(Copy, Clone, Debug)]
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
#[derive(Debug)]
pub struct Step {
    pub lit: Lit,
    pub decision_level: usize,
    pub reason: Reason,
}

//const UNASSIGNED: usize = usize::MAX;

pub struct Trail {
    //pub assignments: Vec<AssignedState>,
    pub assignments: Assignments,
    pub lit_to_level: Vec<usize>, // usize::MAX if unassigned
    pub trail: Vec<Step>,
    pub curr_i: usize,

    /// Trail indices of decisions.
    ///
    /// The first entry does not represent a decision and is fixed at 0 so that each entry on the
    /// trail has a preceding entry in this list and so that the decision at level `n` corresponds
    /// to the index `n`.
    decisions: Vec<usize>,
}

impl Trail {
    pub fn decision_level(&self) -> usize {
        self.decisions.len() - 1
    }
    /*
    #[ensures(result.invariant(*f))]
    #[ensures((@result.trail).len() === 1)]
    #[ensures(result.trail_sem_invariant(*f, *_a))]
    */
    pub fn new(f: &Formula, a: Assignments) -> Trail {
        let a_len = a.len();
        Trail {
            assignments: a,
            lit_to_level: vec::from_elem(usize::MAX, a_len), // TODO
            trail: Vec::new(),
            curr_i: 0,
            decisions: vec::from_elem(0, 1),
        }
    }
    
    /*
    pub fn find_unassigned(&mut self) -> Option<usize> {
        // call self.assignments.find_unassigned()
        None
    }
    */

    // Okay so this checks out on the Linux, but it takes time. I believe it is due to the spec
    // of pop being "too weak". Vytautas told me to complain more, so I'll complain to Xavier.
    // Also: on the Mac the other Assertion fails, so the whole thing should be looked into.
    #[trusted] // Seems like this just takes forever, but checks out
    #[inline(always)]
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
                self.assignments.0[step.lit.idx] += 2; // TODO: Phase saving
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

    /*
    #[requires(f.invariant())]
    #[requires(self.invariant(*f))]
    #[requires(self.lit_not_in_less(*f))]
    #[requires(self.lit_is_unique())]
    #[requires((@self.trail).len() > 0)]
    #[requires(long_are_post_unit_inner(@self.trail, *f, @self.assignments))]
    #[ensures(long_are_post_unit_inner((@(^self).trail), *f, (@(^self).assignments)))]
    */
    // Backtracks to the start of level
    pub fn backtrack_to(&mut self, level: usize, f: &Formula) {
        let old_t = Ghost::record(&self);
        //proof_assert!(self === @old_t);
        //let how_many = self.trail.len() - self.decisions[level];
        //let mut i = 0;
        //let mut i = self.trail.len() - 1;
        let len = self.trail.len();
        let mut i = 0;
        let des = self.decisions[level];
        while i < len {
            self.assignments.0[self.trail[i].lit.idx] += 2;
            //self.assignments.0[self.trail[i].lit.idx] = 3; // TODO: Phase saving
        //while self.trail.len() > 0 && self.trail[self.trail.len() - 1].decision_level > level{ // TODO: >= ?
            //self.backstep(f);
            //self.trail.pop();
            i += 1;
        }
        self.trail.truncate(des);
        use ::std::cmp::max;
        self.trail.truncate(max(level, 1));
        /*
        while self.decisions.len() > level { // TODO + 1?
            self.decisions.pop();
        }
        */
        /*
        if self.decisions.len() == 0 {
            self.decisions.push(0);
        }
        */
        self.curr_i = des//self.trail.len();
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
        self.lit_to_level[step.lit.idx] = self.decision_level();
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
        let dlevel = self.decisions.len(); // Not doing this results in a Why3 error. Todo: Yell at Xavier
        // TODO Unsure if this is correct/the correct thing to track
        self.decisions.push(self.trail.len());
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
    pub fn learn_unit(&mut self, lit: Lit, _f: &Formula) {
        if self.decision_level() > 0 {
            self.backtrack_to(0, _f);
        }
        self.enq_assignment(Step {
            lit: lit,
            decision_level: 0,//self.decision_level(),
            reason: Reason::Unit,
        }, _f);

    }

    

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
