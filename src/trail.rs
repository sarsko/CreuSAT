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
    logic_trail::*,
};

//#[derive(Debug, Eq, PartialEq)]
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
//#[derive(Debug)]
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
    pub decisions: Vec<usize>,
}

impl Trail {
    #[cfg_attr(all(any(trust_trail, trust_all), not(untrust_all)), trusted)]
    #[inline(always)]
    #[requires((@self.decisions).len() > 0)]
    #[ensures(@result === (@self.decisions).len() - 1)]
    pub fn decision_level(&self) -> usize {
        self.decisions.len() - 1
    }
    /*
    #[ensures(result.invariant(*f))]
    #[ensures((@result.trail).len() === 1)]
    #[ensures(result.trail_sem_invariant(*f, *_a))]
    */
    #[cfg_attr(all(any(trust_trail, trust_all), not(untrust_all)), trusted)]
    #[requires(a.invariant(*f))]
    #[ensures(result.invariant(*f))]
    pub fn new(f: &Formula, a: Assignments) -> Trail {
        let a_len = a.len();
        Trail {
            assignments: a,
            lit_to_level: vec::from_elem(usize::MAX, a_len), 
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
    // Should be good. Pop assertion takes forever lol. Either update spec for pop, or
    // add a lemma that says that pop on a seq of positive length is eq to subseq
    #[cfg_attr(all(any(trust_trail, trust_all), not(untrust_all)), trusted)]
    //#[inline(always)]
    #[requires(f.invariant())]
    #[requires(self.invariant(*f))]
    #[ensures((^self).invariant(*f))] // added since last run
    //#[requires(self.lit_not_in_less(*f))]
    //#[requires(self.lit_is_unique())]
    #[requires((@self.trail).len() > 0)]
    #[requires(long_are_post_unit_inner(@self.trail, *f, @self.assignments))]
    #[ensures(long_are_post_unit_inner((@(^self).trail), *f, (@(^self).assignments)))]
    #[ensures((@self.trail).len() === (@(^self).trail).len() + 1)] // added
    fn backstep(&mut self, f: &Formula) {
        let old_t = Ghost::record(&self);
        //proof_assert!(self === @old_t);
        let last = self.trail.pop();
        match last {
            Some(step) => {
                // TODO: Phase saving
                if self.assignments.0[step.lit.idx] < 2 {
                    self.assignments.0[step.lit.idx] += 2; // TODO: Prove safety
                } else {
                    self.assignments.0[step.lit.idx] = 3; // TODO lol
                }
                proof_assert!(@self.assignments == (@(@old_t).assignments).set(@step.lit.idx, 3u8) ||
                @self.assignments == (@(@old_t).assignments).set(@step.lit.idx, 2u8));
                proof_assert!(@self.trail === pop(@(@old_t).trail));
                proof_assert!(^@old_t === ^self);
                proof_assert!((lemma_backtrack_ok(*self, *f, step.lit)); true);
                self.lit_to_level[step.lit.idx] = usize::MAX;
            }
            None => {
                panic!();
            }
        }
    }

    #[cfg_attr(all(any(trust_trail, trust_all), not(untrust_all)), trusted)]
    #[requires((@self.decisions).len() > @level)]
    #[requires(f.invariant())]
    #[maintains((mut self).invariant(*f))]
    #[requires((@self.trail).len() > 0)]
    #[requires(long_are_post_unit_inner(@self.trail, *f, @self.assignments))]
    #[ensures(long_are_post_unit_inner((@(^self).trail), *f, (@(^self).assignments)))]
    // Backtracks to the start of level
    pub fn backtrack_to(&mut self, level: usize, f: &Formula) {
        let old_t = Ghost::record(&self);
        //proof_assert!(self === @old_t);
        let how_many = self.trail.len() - self.decisions[level];
        //let mut i = 0;
        //let mut i = self.trail.len() - 1;
        //let len = self.trail.len();
        // TODO: This correctly fails on the decision invariant.
        // Have to do the proof or do some cheese
        let mut des = self.decisions[level];
        let mut i: usize = 0 ;
        #[invariant(i_less2, @i <= (@(@old_t).trail).len())]
        #[invariant(i_less, i <= how_many)]
        #[invariant(post_unit, long_are_post_unit_inner(@self.trail, *f, @self.assignments))]
        #[invariant(inv, self.invariant(*f))]
        #[invariant(len_is, (@self.trail).len() === (@(@old_t).trail).len() - @i)]
        #[invariant(proph, ^@old_t === ^self)]
        while i < how_many {
            self.backstep(f);
            i += 1;
        }
        //des = i;
        /*
        let mut i = des;
        while i < len {
            /*
            if self.assignments.0[self.trail[i].lit.idx] == 1 {
                self.assignments.0[self.trail[i].lit.idx] += 2;
            } else {
                self.assignments.0[self.trail[i].lit.idx] = 2;
            }
            */
            self.assignments.0[self.trail[i].lit.idx] += 2;
            self.lit_to_level[self.trail[i].lit.idx] = usize::MAX;
            i += 1;
        }
        self.trail.truncate(des);
        */
        self.assignments.1 = 0; // TODO 
        #[invariant(post_unit, long_are_post_unit_inner(@self.trail, *f, @self.assignments))]
        #[invariant(inv, self.invariant(*f))]
        #[invariant(proph, ^@old_t === ^self)]
        while self.decisions.len() > level {
            self.decisions.pop();
        }
        //use ::std::cmp::max;
        //self.decisions.truncate(max(level, 1));
        /*
        use ::std::cmp::min;
        println!("{}", self.curr_i);
        self.curr_i = min(self.curr_i, des);
        if self.curr_i > 0 {
            self.curr_i -= 1;
            //self.curr_i = 0;
            println!("{}", self.curr_i);
            println!("{:?}", self.trail);
            println!("{:?}", self.trail[self.curr_i]);
        }
        */
        // I don't get why setting it to something other than 0 is incorrect
        // Seems to be because we are not handling the asserting level.
        self.curr_i = 0;
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
        //self.curr_i = des//self.trail.len();
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
        self.lit_to_level[step.lit.idx] = self.decision_level();
        let trail = &self.trail;
        self.assignments.set_assignment_new(step.lit, _f, trail);
        proof_assert!(!step.lit.idx_in_trail(self.trail));
        proof_assert!(self.lit_is_unique());
        self.trail.push(step);
        // These four are not checking out
        proof_assert!(self.lit_is_unique()); // Nope
        proof_assert!(self.lit_not_in_less(*_f)); // checking out on Linux
        proof_assert!(long_are_post_unit_inner(@self.trail, *_f, @self.assignments)); // Nope
        proof_assert!(crefs_in_range(@self.trail, *_f)); // This is checking out somehow?
    }

    #[trusted] // TMP
    #[inline(always)]
    pub fn enq_assignment2(&mut self, step: Step, _f: &Formula) {
        self.lit_to_level[step.lit.idx] = self.decision_level();
        self.assignments.0[step.lit.idx] -= 2;
        self.trail.push(step);
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
        self.decisions.push(self.trail.len());
        self.enq_assignment2(Step {
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
            self.backtrack_to(1, _f);
        }
        self.enq_assignment(Step {
            lit: lit,
            decision_level: 0,
            reason: Reason::Unit,
        }, _f);
        //self.decisions[0] += 1;
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
