extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{assignments::*, clause::*, decision::*, formula::*, lit::*, logic::*, solver::SatResult, util::*};

#[cfg(feature = "contracts")]
use crate::logic::{logic::*, logic_trail::*, logic_util::*};

pub enum Reason {
    //Undefined,
    Decision,
    Unit(usize),
    Long(usize),
}

pub struct Step {
    pub lit: Lit,
    pub decision_level: usize,
    pub reason: Reason,
}

pub struct Trail {
    pub assignments: Assignments,
    pub lit_to_level: Vec<usize>, // usize::MAX if unassigned
    pub trail: Vec<Step>,
    pub curr_i: usize,
    pub decisions: Vec<usize>,
}

impl Trail {
    // OK
    #[cfg_attr(feature = "trust_trail", trusted)]
    #[inline(always)]
    #[ensures(@result === (@self.decisions).len())]
    pub fn decision_level(&self) -> usize { self.decisions.len() }
    // OK
    #[cfg_attr(feature = "trust_trail", trusted)]
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

    // For some reason the post takes forever(but it solved on Mac with auto level 3)
    #[cfg_attr(feature = "trust_trail", trusted)]
    #[inline(always)]
    #[requires(f.invariant())]
    #[requires(@f.num_vars > 0)]
    #[requires(self.invariant_no_decision(*f))]
    #[ensures((^self).invariant_no_decision(*f))] // added since last run
    #[requires(long_are_post_unit_inner(@self.trail, *f, @self.assignments))]
    #[ensures(long_are_post_unit_inner((@(^self).trail), *f, (@(^self).assignments)))]
    #[ensures(@result < @f.num_vars)]
    //#[ensures((@self.trail).len() === (@(^self).trail).len() + 1)] // added
    fn backstep(&mut self, f: &Formula) -> usize {
        let old_t = Ghost::record(&self);
        //proof_assert!(self === @old_t);
        let last = self.trail.pop();
        match last {
            Some(step) => {
                if self.assignments.0[step.lit.idx] < 2 {
                    self.assignments.0[step.lit.idx] += 2; // TODO: Prove safety
                } else {
                    self.assignments.0[step.lit.idx] = 3; // TODO lol
                }
                proof_assert!(@self.trail === pop(@(@old_t).trail));
                proof_assert!(^@old_t === ^self);
                proof_assert!((lemma_backtrack_ok(*self, *f, step.lit)); true);
                self.lit_to_level[step.lit.idx] = usize::MAX;
                proof_assert!(long_are_post_unit_inner(@self.trail, *f, @self.assignments));
                return step.lit.idx;
            }
            None => {
                // Could add a req on trail len and prove that this doesn't happen, but
                // not sure if it really is needed.
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
        return 0;
    }

    #[cfg_attr(feature = "trust_trail", trusted)]
    #[inline(always)]
    #[requires(f.invariant())]
    #[maintains((mut self).invariant(*f))]
    #[maintains((mut d).invariant(@f.num_vars))]
    #[requires(long_are_post_unit_inner(@self.trail, *f, @self.assignments))]
    #[ensures(long_are_post_unit_inner((@(^self).trail), *f, (@(^self).assignments)))]
    pub fn backtrack_safe(&mut self, level: usize, f: &Formula, d: &mut Decisions) {
        if level < self.decision_level() {
            self.backtrack_to(level, f, d);
        }
    }

    #[cfg_attr(feature = "trust_trail", trusted)]
    #[requires((@self.decisions).len() > @level)]
    #[requires(f.invariant())]
    #[maintains((mut self).invariant(*f))]
    #[maintains((mut d).invariant(@f.num_vars))]
    //#[requires((@self.trail).len() > 0)] // removed
    #[requires(long_are_post_unit_inner(@self.trail, *f, @self.assignments))]
    #[ensures(long_are_post_unit_inner((@(^self).trail), *f, (@(^self).assignments)))]
    // Backtracks to the start of level
    pub fn backtrack_to(&mut self, level: usize, f: &Formula, d: &mut Decisions) {
        let old_t = Ghost::record(&self);
        let old_d = Ghost::record(&d);
        let how_many = self.trail.len() - self.decisions[level];
        let des = self.decisions[level];
        let mut i: usize = 0;
        let mut curr = d.search;
        let mut timestamp = if curr != usize::MAX { d.linked_list[curr].ts } else { 0 }; // revisit this later
        #[invariant(i_less2, @i <= (@(@old_t).trail).len())]
        #[invariant(i_less, i <= how_many)]
        #[invariant(post_unit, long_are_post_unit_inner(@self.trail, *f, @self.assignments))]
        #[invariant(inv, self.invariant_no_decision(*f))]
        #[invariant(d_inv, d.invariant(@f.num_vars))]
        //#[invariant(len_is, (@self.trail).len() === (@(@old_t).trail).len() - @i)] // we don't care anymore
        #[invariant(proph, ^@old_t === ^self)]
        #[invariant(proph_d, ^@old_d === ^d)]
        #[invariant(curr_less, @curr < (@d.linked_list).len() || @curr === @usize::MAX)]
        // Hmm maybe change invariant
        while i < how_many {
            let idx = self.backstep(f);
            proof_assert!(@idx < @f.num_vars);
            let curr_timestamp = d.linked_list[idx].ts;
            if curr_timestamp > timestamp {
                timestamp = curr_timestamp;
                curr = idx;
            }
            i += 1;
        }
        d.search = curr;

        #[invariant(post_unit, long_are_post_unit_inner(@self.trail, *f, @self.assignments))]
        #[invariant(inv, self.invariant_no_decision(*f))]
        #[invariant(proph, ^@old_t === ^self)]
        while self.decisions.len() > level {
            let old_t2 = Ghost::record(&self);
            proof_assert!(sorted(@self.decisions));
            proof_assert!((@self.decisions).len() > 0);
            proof_assert!(lemma_pop_maintains_sorted(@self.decisions); true);
            match self.decisions.pop() {
                Some(_) => {
                    proof_assert!(@self.decisions === pop(@(@old_t2).decisions));
                    proof_assert!((^@old_t2) === ^self);
                }
                None => {
                    unreachable!();
                }
            }
            proof_assert!(sorted(@self.decisions));
        }
        // This is a noop, and should be proven away.
        #[invariant(post_unit, long_are_post_unit_inner(@self.trail, *f, @self.assignments))]
        #[invariant(inv, self.invariant_no_decision(*f))]
        #[invariant(proph, ^@old_t === ^self)]
        while self.decisions.len() > 0 && self.decisions[self.decisions.len() - 1] > self.trail.len() {
            let old_t3 = Ghost::record(&self);
            proof_assert!(sorted(@self.decisions));
            proof_assert!((@self.decisions).len() > 0);
            proof_assert!(lemma_pop_maintains_sorted(@self.decisions); true);
            //proof_assert!((@self.decisions) == (@(@old_trail).decisions));
            match self.decisions.pop() {
                Some(_) => {
                    proof_assert!((@self.decisions) === pop(@(@old_t3).decisions));
                    proof_assert!((^@old_t3) === ^self);
                }
                None => {
                    unreachable!();
                }
            }
            proof_assert!(lemma_pop_maintains_sorted(@(@old_t3).decisions); true);
            proof_assert!(sorted(@self.decisions));
        }
        proof_assert!(
            (@self.decisions).len() === 0 ||
            @(@self.decisions)[(@self.decisions).len()-1] <= (@self.trail).len()
        );
        proof_assert!(decisions_invariant(@self.decisions, @self.trail));
        proof_assert!(self.assignments.invariant(*f));
        proof_assert!(trail_invariant(@self.trail, *f));
        proof_assert!(lit_to_level_invariant(@self.lit_to_level, *f));
        proof_assert!(self.lit_not_in_less(*f));
        proof_assert!(self.lit_is_unique());
        proof_assert!(long_are_post_unit_inner(@self.trail, *f, @self.assignments));
        proof_assert!(self.trail_entries_are_assigned());

        self.curr_i = level;
        //self.curr_i = self.trail.len();
    }

    // Could help it a bit in seeing that unit are sat
    #[cfg_attr(feature = "trust_trail", trusted)]
    #[maintains((mut self).invariant(*_f))]
    #[requires(_f.invariant())]
    #[requires(step.lit.invariant(@_f.num_vars))]
    #[requires(step.invariant(*_f))]
    #[requires(match step.reason {
        Reason::Long(cref) => {@cref < (@_f.clauses).len()
                            && (@_f.clauses)[@cref].unit(self.assignments)
                            && step.lit.lit_in((@_f.clauses)[@cref])}, // Changed
        Reason::Unit(cref) => {@cref < (@_f.clauses).len()
                            && step.lit === (@(@_f.clauses)[@cref])[0]},
        _                  => true,
    })]
    #[requires(!step.lit.idx_in_trail(self.trail))]
    #[requires(unset((@self.assignments)[@step.lit.idx]))]
    #[requires(long_are_post_unit_inner(@self.trail, *_f, @self.assignments))]
    #[ensures((forall<j : Int> 0 <= j && j < (@self.assignments).len() &&
        j != @step.lit.idx ==> (@self.assignments)[j] === (@(^self).assignments)[j]))]
    #[ensures(step.lit.sat((^self).assignments))]
    #[ensures(long_are_post_unit_inner((@(^self).trail), *_f, (@(^self).assignments)))]
    #[ensures(match step.reason {
        Reason::Long(k) => clause_post_with_regards_to_lit((@_f.clauses)[@k], (^self).assignments, step.lit),
        _               => true
    })]
    #[ensures((@(^self).trail).len() === 1 + (@self.trail).len())]
    #[ensures((^self).decisions === self.decisions)] // added
    pub fn enq_assignment(&mut self, step: Step, _f: &Formula) {
        self.lit_to_level[step.lit.idx] = self.decision_level();
        let trail = &self.trail;

        self.assignments.set_assignment(step.lit, _f, trail);

        proof_assert!(lit_not_in_less_inner(@self.trail, *_f));
        proof_assert!(step.invariant(*_f));
        proof_assert!(lemma_push_maintains_lit_not_in_less(*self, *_f, step); true);
        self.trail.push(step);
        proof_assert! {
            match step.reason {
                Reason::Long(k) => { clause_post_with_regards_to_inner((@_f.clauses)[@k], @(*self).assignments, @step.lit.idx) },
                    _ => true,
                }
        };

        proof_assert!(self.lit_is_unique());
        proof_assert!(self.lit_not_in_less(*_f));

        proof_assert!(long_are_post_unit_inner(@self.trail, *_f, @self.assignments));
    }

    // Checks out on mac with introduction of lemma. For some reason trail_entries_are_assigned
    // is now slowest. Should be solveable by another lemma
    #[cfg_attr(feature = "trust_trail", trusted)]
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
        let trail_len = self.trail.len();
        self.decisions.push(trail_len);
        let dlevel = self.decisions.len(); // Not doing this results in a Why3 error. Todo: Yell at Xavier
        self.lit_to_level[idx] = dlevel;
        self.assignments.0[idx] -= 2;
        let lit = Lit {
            idx: idx,
            // This branch duplicates the proofs... finding some way to factor this would x2 the proof
            polarity: if self.assignments.0[idx] == 0 { false } else { true },
        }; // TODO encapsulate
        let step = Step { lit: lit, decision_level: dlevel, reason: Reason::Decision };

        self.trail.push(step);
        proof_assert!(self.lit_not_in_less(*_f));
        // TODO: Check that this lemma is actually being applied, it doesn't seem like it...
        proof_assert!(lemma_assign_maintains_long_are_post_unit2(@self.trail, *_f, self.assignments, idx); true);
        proof_assert!(long_are_post_unit_inner(@self.trail, *_f, @self.assignments));
        // This is just the trail invariant unwrapped
        proof_assert!(trail_invariant(@self.trail, *_f));

        proof_assert!(self.lit_is_unique());
        proof_assert!(self.trail_entries_are_assigned());
    }

    // Okay so I should really just prove the backtracking mechanism, this is not nice
    #[cfg_attr(feature = "trust_trail", trusted)]
    #[maintains((mut self).invariant(*f))]
    #[maintains((mut d).invariant(@f.num_vars))]
    #[requires(f.invariant())]
    #[requires(@cref < (@f.clauses).len())]
    #[requires((@(@f.clauses)[@cref]).len() == 1)]
    #[requires((@f.clauses)[@cref].invariant(@f.num_vars))]
    // unsure which of these is wanted
    //#[ensures(@f.clauses)[@cref].sat((^self).assignments))]
    #[ensures(match result {
        Err(_) => true,
        Ok(_) => (@(@f.clauses)[@cref])[0].sat((^self).assignments)})]
    #[requires(long_are_post_unit_inner(@self.trail, *f, @self.assignments))]
    #[ensures(long_are_post_unit_inner((@(^self).trail), *f, (@(^self).assignments)))]
    pub fn learn_unit(&mut self, cref: usize, f: &Formula, d: &mut Decisions) -> Result<(), ()> {
        if self.decision_level() > 0 {
            self.backtrack_to(0, f, d);
        }
        // I have to do a proof here that it is unset after ->
        // will need another requires
        if f.clauses[cref].rest[0].lit_set(&self.assignments) {
            return Err(()); // UGLY Runtime check
        }
        self.enq_assignment(Step { lit: f.clauses[cref].rest[0], decision_level: 0, reason: Reason::Unit(cref) }, f);
        Ok(())
    }

    #[cfg_attr(feature = "trust_trail", trusted)]
    #[maintains((mut self).invariant(*f))]
    #[maintains((mut d).invariant(@f.num_vars))]
    #[requires(f.invariant())]
    #[ensures(match result {
        Some(cref) => @cref < (@f.clauses).len()
                   && (@(@f.clauses)[@cref]).len() == 1
                   && (@f.clauses)[@cref].unsat((^self).assignments)
                   && (@(@f.clauses)[@cref])[0].unsat((^self).assignments),
        _ => true,
    })]
    pub fn learn_units(&mut self, f: &Formula, d: &mut Decisions) -> Option<usize> {
        let mut i = 0;
        let old_d = Ghost::record(&d);
        let old_self = Ghost::record(&self);
        #[invariant(self_inv, self.invariant(*f))]
        #[invariant(proph, ^@old_self === ^self)]
        #[invariant(proph_d, ^@old_d === ^d)]
        #[invariant(d_inv, d.invariant(@f.num_vars))]
        while i < f.clauses.len() {
            let clause = &f.clauses[i];
            if clause.rest.len() == 1 {
                let lit = clause.rest[0];
                // This check should be removed by an invariant that the formula only contains unique clauses
                if lit.lit_set(&self.assignments) {
                    if lit.lit_unsat(&self.assignments) {
                        return Some(i);
                    }
                } else {
                    self.learn_unit(i, f, d);
                }
            }
            i += 1;
        }
        return None;
    }
}
