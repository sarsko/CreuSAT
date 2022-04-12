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
//#[derive(Eq, PartialEq)]
pub enum Reason {
    //Undefined,
    Decision,
    Unit(usize),
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
    // OK
    #[cfg_attr(all(any(trust_trail, trust_all), not(untrust_all)), trusted)]
    #[inline(always)]
    #[ensures(@result === (@self.decisions).len())]
    pub fn decision_level(&self) -> usize {
        self.decisions.len()
    }
    // OK
    #[cfg_attr(all(any(trust_trail, trust_all), not(untrust_all)), trusted)]
    #[requires(f.invariant())]
    #[requires(a.invariant(*f))]
    #[ensures(result.invariant(*f))]
    pub fn new(f: &Formula, a: Assignments) -> Trail {
        Trail {
            assignments: a,
            lit_to_level: vec::from_elem(usize::MAX, f.num_vars), 
            trail: Vec::new(),
            curr_i: 0,
            decisions: Vec::new(),
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

    // Okay so if one updates the spec for pop it checks out
    #[cfg_attr(all(any(trust_trail, trust_all), not(untrust_all)), trusted)]
    //#[inline(always)]
    #[requires(f.invariant())]
    #[requires(self.invariant_no_decision(*f))]
    #[ensures((^self).invariant_no_decision(*f))] // added since last run
    //#[requires(self.lit_not_in_less(*f))]
    //#[requires(self.lit_is_unique())]
    //#[requires((@self.trail).len() > 0)]
    #[requires(long_are_post_unit_inner(@self.trail, *f, @self.assignments))]
    #[ensures(long_are_post_unit_inner((@(^self).trail), *f, (@(^self).assignments)))]
    //#[ensures((@self.trail).len() === (@(^self).trail).len() + 1)] // added
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
                //panic!(); // does it matter?
                // Could add a req on trail len and prove that this doesn't happen, but
                // not sure if it really is needed.
                proof_assert!(@self.trail == @(@old_t).trail);
                proof_assert!(long_are_post_unit_inner(@self.trail, *f, @self.assignments));
            }
        }
        proof_assert!(self.assignments.invariant(*f));
        proof_assert!(trail_invariant(@self.trail, *f));
        proof_assert!(lit_to_level_invariant(@self.lit_to_level, *f));
        //proof_assert!(decisions_invariant(@self.decisions, @self.trail));
        proof_assert!(self.lit_not_in_less(*f));
        proof_assert!(self.lit_is_unique());
        proof_assert!(long_are_post_unit_inner(@self.trail, *f, @self.assignments));
        proof_assert!(self.trail_entries_are_assigned());
    }

    // Only pop FAILING 
    #[cfg_attr(all(any(trust_trail, trust_all), not(untrust_all)), trusted)]
    #[requires((@self.decisions).len() > @level)]
    #[requires(f.invariant())]
    #[maintains((mut self).invariant(*f))]
    //#[requires((@self.trail).len() > 0)] // removed
    #[requires(long_are_post_unit_inner(@self.trail, *f, @self.assignments))]
    #[ensures(long_are_post_unit_inner((@(^self).trail), *f, (@(^self).assignments)))]
    // Backtracks to the start of level
    pub fn backtrack_to(&mut self, level: usize, f: &Formula) {
        let old_t = Ghost::record(&self);
        let how_many = self.trail.len() - self.decisions[level];
        let des = self.decisions[level];
        let mut i: usize = 0 ;
        #[invariant(i_less2, @i <= (@(@old_t).trail).len())]
        #[invariant(i_less, i <= how_many)]
        #[invariant(post_unit, long_are_post_unit_inner(@self.trail, *f, @self.assignments))]
        #[invariant(inv, self.invariant_no_decision(*f))]
        //#[invariant(len_is, (@self.trail).len() === (@(@old_t).trail).len() - @i)] // we don't care anymore
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
        // Prove this later
        #[invariant(post_unit, long_are_post_unit_inner(@self.trail, *f, @self.assignments))]
        #[invariant(inv, self.invariant_no_decision(*f))]
        #[invariant(proph, ^@old_t === ^self)]
        while self.decisions.len() > level {
            let old_trail = Ghost::record(&self);
            proof_assert!(sorted(@self.decisions));
            proof_assert!((@self.decisions).len() > 0);
            proof_assert!(lemma_pop_maintains_sorted(@self.decisions); true);
            proof_assert!((^@old_trail) === ^self);
            self.decisions.pop();
            proof_assert!((@self.decisions) === pop(@(@old_trail).decisions));
            proof_assert!(sorted(@self.decisions));
        }
        // This is a noop, and should be proven away.
        #[invariant(post_unit, long_are_post_unit_inner(@self.trail, *f, @self.assignments))]
        #[invariant(inv, self.invariant_no_decision(*f))]
        #[invariant(proph, ^@old_t === ^self)]
        /*
        #[invariant(loop_cond,
            (@self.decisions).len() > 0 && @(@self.decisions)[(@self.decisions).len()-1] <= @level
        )]
        */
        while self.decisions.len() > 0 && self.decisions[self.decisions.len() - 1] > self.trail.len() {
            let old_trail = Ghost::record(&self);
            proof_assert!(sorted(@self.decisions));
            proof_assert!((@self.decisions).len() > 0);
            proof_assert!(lemma_pop_maintains_sorted(@self.decisions); true);
            //proof_assert!((@self.decisions) == (@(@old_trail).decisions));
            self.decisions.pop();
            proof_assert!((@self.decisions) == pop(@(@old_trail).decisions));
            proof_assert!(lemma_pop_maintains_sorted(@(@old_trail).decisions); true);
            proof_assert!((^@old_trail) === ^self);
            proof_assert!(sorted(@self.decisions));
        }
        proof_assert!(
            (@self.decisions).len() === 0 ||
            @(@self.decisions)[(@self.decisions).len()-1] <= (@self.trail).len()
        );
        proof_assert!(decisions_invariant(@self.decisions, @self.trail));
        //proof_assert!(self.invariant(*f));
        proof_assert!(self.assignments.invariant(*f));
        proof_assert!(trail_invariant(@self.trail, *f));
        proof_assert!(lit_to_level_invariant(@self.lit_to_level, *f));
        proof_assert!(self.lit_not_in_less(*f));
        proof_assert!(self.lit_is_unique());
        proof_assert!(long_are_post_unit_inner(@self.trail, *f, @self.assignments));
        proof_assert!(self.trail_entries_are_assigned());
        //use ::std::cmp::max;
        //self.decisions.truncate(max(level, 1));
        /*
        if self.decisions.len() == 0 {
            self.decisions.push(0);
        }
        */
        //self.curr_i = des//self.trail.len();
        // I don't get why setting it to something other than 0 is incorrect
        // Seems to be because we are not handling the asserting level.
        self.curr_i = 0;
    }


    // Checks out on mac with introduction of lemma.
    // Can be made even faster with some more lemmas.
    #[cfg_attr(all(any(trust_trail, trust_all), not(untrust_all)), trusted)]
    #[maintains((mut self).invariant(*_f))]
    #[requires(_f.invariant())]
    #[requires(step.lit.invariant(@_f.num_vars))]
    #[requires(match step.reason {
        Reason::Long(k) => 0 <= @k && @k < (@_f.clauses).len() &&
        (@_f.clauses)[@k].unit(self.assignments) 
        && step.lit.lit_in((@_f.clauses)[@k]), // Changed
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
    #[ensures(match step.reason {
        Reason::Long(k) => clause_post_with_regards_to_lit((@_f.clauses)[@k], (^self).assignments, step.lit),
        _ => true
    })]
    #[ensures((@(^self).trail).len() === 1 + (@self.trail).len())]
    #[ensures((^self).decisions === self.decisions)] // added
    pub fn enq_assignment(&mut self, step: Step, _f: &Formula) {
        self.lit_to_level[step.lit.idx] = self.decision_level();
        let trail = &self.trail;
        let old_self = Ghost::record(&self);
        proof_assert!(unset((@(@old_self).assignments)[@step.lit.idx]));
        self.assignments.set_assignment(step.lit, _f, trail);
        proof_assert!(lit_not_in_less_inner(@self.trail, *_f));
        proof_assert!(step.invariant(*_f));
        proof_assert!(lemma_push_maintains_lit_not_in_less(*self, *_f, step); true);
        self.trail.push(step);
        proof_assert!((@(@old_self).trail).push(step) === @self.trail);
        proof_assert!(^@old_self === ^self);
        proof_assert!(lit_not_in_less_inner(@self.trail, *_f));
        proof_assert!(self.lit_not_in_less(*_f)); 
        proof_assert!(long_are_post_unit_inner(@self.trail, *_f, @self.assignments));

        // This is just the trail invariant unwrapped
        /*
        proof_assert!(self.assignments.invariant(*_f));
        proof_assert!(trail_invariant(@self.trail, *_f));
        proof_assert!(lit_to_level_invariant(@self.lit_to_level, *_f));
        proof_assert!(decisions_invariant(@self.decisions, @self.trail));
        proof_assert!(self.lit_not_in_less(*_f));
        proof_assert!(self.lit_is_unique());
        proof_assert!(long_are_post_unit_inner(@self.trail, *_f, @self.assignments));
        proof_assert!(self.trail_entries_are_assigned());
        */
    }


    // Checks out on mac with introduction of lemma. For some reason trail_entries_are_assigned
    // is now slowest. Should be solveable by another lemma
    #[cfg_attr(all(any(trust_trail, trust_all), not(untrust_all)), trusted)]
    #[requires(_f.invariant())]
    #[maintains((mut self).invariant(*_f))]
    #[requires(@idx < @_f.num_vars)]
    //#[requires(@(@self.assignments)[@idx] <= 3)] // This will trickle everywhere(add as invariant?)
    #[requires(unset((@self.assignments)[@idx]))]
    #[ensures((forall<j : Int> 0 <= j && j < (@self.assignments).len() &&
        j != @idx ==> (@self.assignments)[j] === (@(^self).assignments)[j]))]
    #[ensures(@(@(^self).assignments)[@idx] === 1 || @(@(^self).assignments)[@idx] === 0)] // Is this needed?
    #[requires(long_are_post_unit_inner(@self.trail, *_f, @self.assignments))]
    #[ensures(long_are_post_unit_inner((@(^self).trail), *_f, (@(^self).assignments)))]
    #[ensures((@(^self).trail).len() === 1 + (@self.trail).len())]
    pub fn enq_decision(&mut self, idx: usize, _f: &Formula) {
        let old_self = Ghost::record(&self);
        let trail_len = self.trail.len();
        self.decisions.push(trail_len);
        let dlevel = self.decisions.len(); // Not doing this results in a Why3 error. Todo: Yell at Xavier
        self.lit_to_level[idx] = dlevel;
        proof_assert!(lemma_assign_maintains_long_are_post_unit2(@self.trail, *_f, self.assignments, idx); true);
        let old_self = Ghost::record(&self);
        proof_assert!(unset((@(@old_self).assignments)[@idx]));
        self.assignments.0[idx] -= 2;
        proof_assert!(@self.assignments == (@(@old_self).assignments).set(@idx, 0u8) ||
                      @self.assignments == (@(@old_self).assignments).set(@idx, 1u8));
        proof_assert!(lemma_assign_maintains_long_are_post_unit2(@self.trail, *_f, self.assignments, idx); true);
        proof_assert!(^@old_self === ^self);
        proof_assert!(long_are_post_unit_inner(@self.trail, *_f, @self.assignments));
        let lit = Lit{ idx: idx, polarity: if self.assignments.0[idx] == 0 {false} else {true} }; // TODO encapsulate
        let step = Step {
            lit: lit,
            decision_level: dlevel,
            reason: Reason::Decision,
        };
        proof_assert!(lit_not_in_less_inner(@self.trail, *_f));
        proof_assert!(step.invariant(*_f));
        proof_assert!(lemma_push_maintains_lit_not_in_less(*self, *_f, step); true);
        self.trail.push(step);
        proof_assert!((@(@old_self).trail).push(step) === @self.trail);
        proof_assert!(^@old_self === ^self);
        proof_assert!(lit_not_in_less_inner(@self.trail, *_f));
        proof_assert!(self.lit_not_in_less(*_f));
        proof_assert!(long_are_post_unit_inner(@self.trail, *_f, @self.assignments));
        // This is just the trail invariant unwrapped
        proof_assert!(self.assignments.invariant(*_f));
        proof_assert!(trail_invariant(@self.trail, *_f));
        proof_assert!(lit_to_level_invariant(@self.lit_to_level, *_f));
        proof_assert!(decisions_invariant(@self.decisions, @self.trail));
        proof_assert!(self.lit_is_unique());
        //proof_assert!(self.lit_not_in_less(*_f)); 
        //proof_assert!(long_are_post_unit_inner(@self.trail, *_f, @self.assignments));
        proof_assert!(self.trail_entries_are_assigned());
    }

    #[cfg_attr(all(any(trust_trail, trust_all), not(untrust_all)), trusted)]
    #[maintains((mut self).invariant(*f))]
    #[requires(f.invariant())]
    #[requires(@cref < (@f.clauses).len())]
    #[requires((@(@f.clauses)[@cref]).len() == 1)]
    #[requires((@f.clauses)[@cref].invariant(@f.num_vars))]
    // unsure which of these is wanted
    //#[ensures(@f.clauses)[@cref].sat((^self).assignments))]
    #[ensures((@(@f.clauses)[@cref])[0].sat((^self).assignments))]
    #[requires(long_are_post_unit_inner(@self.trail, *f, @self.assignments))]
    #[ensures(long_are_post_unit_inner((@(^self).trail), *f, (@(^self).assignments)))]
    pub fn learn_unit(&mut self, cref: usize, f: &Formula) {
        if self.decision_level() > 0 {
            self.backtrack_to(0, f);
        }
        // I have to do a proof here that it is unset after ->
        // will need another requires
        //proof_assert!(unset((@self.assignments)[@lit.idx])); // TODO
        //proof_assert!(!lit.idx_in_trail(self.trail)); // TODO
        self.enq_assignment(Step {
            lit: f.clauses[cref].rest[0],
            decision_level: 0,
            reason: Reason::Unit(cref),
        }, f);
    }

    /*
    #[cfg_attr(all(any(trust_trail, trust_all), not(untrust_all)), trusted)]
    #[maintains((mut self).invariant(*_f))]
    #[requires(_f.invariant())]
    #[requires(lit.invariant(@_f.num_vars))]
    #[ensures(lit.sat((^self).assignments))]
    #[requires(long_are_post_unit_inner(@self.trail, *f, @self.assignments))]
    #[ensures(long_are_post_unit_inner((@(^self).trail), ^f, (@(^self).assignments)))]
    pub fn add_and_enq_unit(&mut self, lit: Lit, f: &mut Formula) {
        if self.decision_level() > 0 {
            self.backtrack_to(0, _f);
        }
        // I have to do a proof here that it is unset after ->
        // will need another requires
        proof_assert!(unset((@self.assignments)[@lit.idx])); // TODO
        proof_assert!(!lit.idx_in_trail(self.trail)); // TODO
        self.enq_assignment(Step {
            lit: lit,
            decision_level: 0,
            reason: Reason::Unit(cref),
        }, _f);
    }
    */

    // TODO on returning something better than false
    #[cfg_attr(all(any(trust_trail, trust_all), not(untrust_all)), trusted)]
    #[requires(f.invariant())]
    #[maintains((mut self).invariant(*f))]
    pub fn learn_units(&mut self, f: &Formula) -> bool {
        let mut i = 0;
        let old_self = Ghost::record(&self);
        #[invariant(self_inv, self.invariant(*f))]
        #[invariant(proph, ^@old_self === ^self)]
        while i < f.clauses.len() {
            let clause = &f.clauses[i];
            if clause.rest.len() == 1 {
                let lit = clause.rest[0];
                if lit.lit_unset(&self.assignments) {
                    return false;
                }
                self.learn_unit(i, f);
            }
            i += 1;
        }
        return true;
    }

    /*
    #[cfg_attr(all(any(trust_trail, trust_all), not(untrust_all)), trusted)]
    #[maintains((mut self).invariant(*f))]
    #[requires(f.invariant())]
    #[requires(lit.invariant(@.num_vars))]
    #[ensures(lit.sat((^self).assignments))]
    #[requires(long_are_post_unit_inner(@self.trail, *f, @self.assignments))]
    #[ensures(long_are_post_unit_inner((@(^self).trail), *f, (@(^self).assignments)))]
    pub fn learn_unit_add_to_formula(&mut self, lit: Lit, f: &Formula) {
        if self.decision_level() > 0 {
            self.backtrack_to(0, _f);
        }
        // I have to do a proof here that it is unset after ->
        // will need another requires
        proof_assert!(unset((@self.assignments)[@lit.idx])); // TODO
        proof_assert!(!lit.idx_in_trail(self.trail)); // TODO
        let cref = f.add_unwatched_clause(lit);
        self.enq_assignment(Step {
            lit: lit,
            decision_level: 0,
            reason: Reason::Unit(cref),
        }, _f);
    }
    */
}
