use creusot_contracts::{std::*, Snapshot, *};

use crate::{assignments::*, decision::*, formula::*, lit::*};

#[cfg(creusot)]
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
    #[ensures(result@ == self.decisions@.len())]
    pub fn decision_level(&self) -> usize {
        self.decisions.len()
    }

    // OK
    #[cfg_attr(feature = "trust_trail", trusted)]
    #[requires(f.inv())]
    #[requires(a.inv(*f))]
    #[ensures(result.inv(*f))]
    pub fn new(f: &Formula, a: Assignments) -> Trail {
        Trail {
            assignments: a,
            lit_to_level: vec::from_elem(usize::MAX, f.num_vars),
            trail: Vec::new(),
            curr_i: 0,
            decisions: Vec::new(),
        }
    }

    #[cfg_attr(all(feature = "trust_trail", not(feature = "problem_child")), trusted)]
    #[inline(always)]
    #[requires(f.inv())]
    #[requires(f.num_vars@ > 0)]
    #[maintains((mut self).inv_no_decision(*f))]
    #[requires(long_are_post_unit_inner(self.trail@, *f, self.assignments@))]
    #[ensures(long_are_post_unit_inner((^self).trail@, *f, (^self).assignments@))]
    #[ensures(result@ < f.num_vars@)]
    //#[ensures((self@.trail).len() == (@(^self).trail).len() + 1)] // added
    fn backstep(&mut self, f: &Formula) -> usize {
        let old_t: Snapshot<&mut Trail> = snapshot! { self };
        //proof_assert!(self == old_t@);
        let last = self.trail.pop();
        match last {
            Some(step) => {
                // TODO: Wrap in abstraction
                self.assignments[step.lit.index()] += 2;

                proof_assert!(self.trail@ == pop(old_t.trail@));
                proof_assert!(^old_t.inner() == ^self);

                self.lit_to_level[step.lit.index()] = usize::MAX;

                proof_assert!(long_are_post_unit_inner(self.trail@, *f, self.assignments@));
                return step.lit.index();
            }
            None => {
                // Could add a req on trail len and prove that this doesn't happen, but
                // not sure if it really is needed.
                proof_assert!(long_are_post_unit_inner(self.trail@, *f, self.assignments@) && true);
            }
        }
        proof_assert!(self.assignments.inv(*f));
        // proof_assert!(trail_invariant(self@.trail, *f));
        // proof_assert!(lit_to_level_invariant(self@.lit_to_level, *f));
        //proof_assert!(decisions_invariant(self@.decisions, self@.trail));
        //proof_assert!(self.lit_not_in_less(*f));
        //proof_assert!(self.lit_is_unique());
        proof_assert!(long_are_post_unit_inner(self.trail@, *f, self.assignments@));
        //proof_assert!(self.trail_entries_are_assigned());
        return 0;
    }

    #[cfg_attr(feature = "trust_trail", trusted)]
    #[inline(always)]
    #[requires(f.inv())]
    #[maintains((mut self).inv(*f))]
    #[maintains((mut d).inv(f.num_vars@))]
    #[requires(long_are_post_unit_inner(self.trail@, *f, self.assignments@))]
    #[ensures(long_are_post_unit_inner((^self).trail@, *f, (^self).assignments@))]
    pub fn backtrack_safe(&mut self, level: usize, f: &Formula, d: &mut Decisions) {
        if level < self.decision_level() {
            self.backtrack_to(level, f, d);
        }
    }

    #[cfg_attr(feature = "trust_trail", trusted)]
    #[requires(self.decisions@.len() > level@)]
    #[requires(f.inv())]
    #[maintains((mut self).inv(*f))]
    #[maintains((mut d).inv(f.num_vars@))]
    //#[requires((self@.trail).len() > 0)] // removed
    #[requires(long_are_post_unit_inner(self.trail@, *f, self.assignments@))]
    #[ensures(long_are_post_unit_inner((^self).trail@, *f, (^self).assignments@))]
    // Backtracks to the start of level
    pub fn backtrack_to(&mut self, level: usize, f: &Formula, d: &mut Decisions) {
        let old_t: Snapshot<&mut Trail> = snapshot! { self };
        let old_d: Snapshot<&mut Decisions> = snapshot! { d };
        let how_many = self.trail.len() - self.decisions[level];
        let des = self.decisions[level];
        let mut i: usize = 0;
        let mut curr = d.search;
        let mut timestamp = if curr != usize::MAX { d.linked_list[curr].ts } else { 0 }; // revisit this later
        #[invariant(i@ <= old_t.trail@.len())]
        #[invariant(i <= how_many)]
        #[invariant(long_are_post_unit_inner(self.trail@, *f, self.assignments@))]
        #[invariant(self.inv_no_decision(*f))]
        #[invariant(d.inv(f.num_vars@))]
        //#[invariant((self@.trail).len() == old_t.trail@.len() - i@)] // we don't care anymore
        #[invariant(curr@ < d.linked_list@.len() || curr@ == usize::MAX@)]
        // Hmm maybe change invariant
        while i < how_many {
            let idx = self.backstep(f);
            proof_assert!(idx@ < f.num_vars@);
            let curr_timestamp = d.linked_list[idx].ts;
            if curr_timestamp > timestamp {
                timestamp = curr_timestamp;
                curr = idx;
            }
            i += 1;
        }
        d.search = curr;

        #[invariant(long_are_post_unit_inner(self.trail@, *f, self.assignments@))]
        #[invariant(self.inv_no_decision(*f))]
        while self.decisions.len() > level {
            let old_t2: Snapshot<&mut Trail> = snapshot! { self };
            proof_assert!(sorted(self.decisions@));
            proof_assert!(self.decisions@.len() > 0);
            proof_assert!(lemma_pop_maintains_sorted(self.decisions@); true);
            match self.decisions.pop() {
                Some(_) => {
                    proof_assert!(self.decisions@ == pop(old_t2.decisions@));
                    proof_assert!((^old_t2.inner()) == ^self);
                }
                None => {
                    unreachable!();
                }
            }
            proof_assert!(sorted(self.decisions@));
        }
        // This is a noop, and should be proven away.
        #[invariant(long_are_post_unit_inner(self.trail@, *f, self.assignments@))]
        #[invariant(self.inv_no_decision(*f))]
        while self.decisions.len() > 0 && self.decisions[self.decisions.len() - 1] > self.trail.len() {
            let old_t3: Snapshot<&mut Trail> = snapshot! { self };
            proof_assert!(sorted(self.decisions@));
            proof_assert!(self.decisions@.len() > 0);
            proof_assert!(lemma_pop_maintains_sorted(self.decisions@); true);
            //proof_assert!((self@.decisions) == old_trail@.decisions));
            match self.decisions.pop() {
                Some(_) => {
                    proof_assert!(self.decisions@ == pop(old_t3.decisions@));
                    proof_assert!((^old_t3.inner()) == ^self);
                }
                None => {
                    unreachable!();
                }
            }
            proof_assert!(lemma_pop_maintains_sorted(old_t3.decisions@); true);
            proof_assert!(sorted(self.decisions@));
        }
        proof_assert!(
            self.decisions@.len() == 0 ||
            self.decisions@[self.decisions@.len()-1]@ <= self.trail@.len()
        );
        // proof_assert!(decisions_invariant(self@.decisions, self@.trail));
        proof_assert!(self.assignments.inv(*f));
        // proof_assert!(trail_invariant(self@.trail, *f));
        // proof_assert!(lit_to_level_invariant(self@.lit_to_level, *f));
        //proof_assert!(self.lit_not_in_less(*f));
        //proof_assert!(self.lit_is_unique());
        proof_assert!(long_are_post_unit_inner(self.trail@, *f, self.assignments@));
        //proof_assert!(self.trail_entries_are_assigned());

        self.curr_i = level;
        //self.curr_i = self.trail.len();
    }

    #[cfg_attr(feature = "trust_trail", trusted)]
    #[maintains((mut self).inv(*_f))]
    #[requires(_f.inv())]
    #[requires(step.lit.inv(_f.num_vars@))]
    #[requires(step.reason.inv(*_f))]
    #[requires(match step.reason {
        Reason::Long(cref) => {cref@ < _f.clauses@.len()
                            && _f.clauses@[cref@]@[0].unset(self.assignments)
                            && (forall<i: Int> 1 <= i && i < _f.clauses@[cref@]@.len() ==>
                                _f.clauses@[cref@]@[i].unsat(self.assignments))
                            && _f.clauses@[cref@]@[0] == step.lit
                            },
                            //&& step.lit.lit_in((_f.clauses@)[cref@])}, // Changed
                            //&& (_f.clauses@)[cref@].unit(self.assignments)
                            //&& step.lit.lit_in((_f.clauses@)[cref@])}, // Changed
        Reason::Unit(cref) => {cref@ < _f.clauses@.len()
                            && step.lit == _f.clauses@[cref@]@[0]},
        _                  => true,
    })]
    #[requires(!step.lit.idx_in_trail(self.trail))]
    #[requires(unset(self.assignments@[step.lit.index_logic()]))] // Should not be needed anymore
    #[requires(long_are_post_unit_inner(self.trail@, *_f, self.assignments@))]
    #[ensures((forall<j: Int> 0 <= j && j < self.assignments@.len() &&
        j != step.lit.index_logic() ==> self.assignments@[j] == (^self).assignments@[j]))]
    #[ensures(step.lit.sat((^self).assignments))]
    #[ensures(long_are_post_unit_inner((^self).trail@, *_f, (^self).assignments@))]
    #[ensures(match step.reason {
        Reason::Long(k) => clause_post_with_regards_to_lit(_f.clauses@[k@], (^self).assignments, step.lit),
        _               => true
    })]
    #[ensures((^self).trail@.len() == 1 + self.trail@.len())]
    #[ensures((^self).decisions == self.decisions)] // added
    pub fn enq_assignment(&mut self, step: Step, _f: &Formula) {
        self.lit_to_level[step.lit.index()] = self.decision_level();
        let trail = &self.trail;

        self.assignments.set_assignment(step.lit, _f, trail);

        //proof_assert!(step.inv(*_f));
        proof_assert!(lemma_push_maintains_lit_not_in_less(*self, *_f, step); true);
        self.trail.push(step);

        //proof_assert!(self.lit_is_unique());
        //proof_assert!(self.lit_not_in_less(*_f));

        proof_assert!(long_are_post_unit_inner(self.trail@, *_f, self.assignments@));
    }

    #[cfg_attr(feature = "trust_trail", trusted)]
    #[requires(_f.inv())]
    #[maintains((mut self).inv(*_f))]
    #[requires(idx@ < _f.num_vars@)]
    #[requires(unset(self.assignments@[idx@]))]
    #[ensures((forall<j: Int> 0 <= j && j < self.assignments@.len() &&
        j != idx@ ==> self.assignments@[j] == (^self).assignments@[j]))]
    #[ensures((^self).assignments@[idx@]@ == 1 || (^self).assignments@[idx@]@ == 0)] // Is this needed?
    #[requires(long_are_post_unit_inner(self.trail@, *_f, self.assignments@))]
    #[ensures(long_are_post_unit_inner((^self).trail@, *_f, (^self).assignments@))]
    #[ensures((^self).trail@.len() == 1 + self.trail@.len())]
    pub fn enq_decision(&mut self, idx: usize, _f: &Formula) {
        let trail_len = self.trail.len();
        self.decisions.push(trail_len);
        let dlevel = self.decisions.len(); // Not doing this results in a Why3 error. Todo: Yell at Xavier
        self.lit_to_level[idx] = dlevel;
        self.assignments[idx] -= 2;
        let lit = Lit::phase_saved(idx, &self.assignments);

        let step = Step { lit: lit, decision_level: dlevel, reason: Reason::Decision };

        self.trail.push(step);
    }

    // Okay so I should really just prove the backtracking mechanism, this is not nice
    #[cfg_attr(feature = "trust_trail", trusted)]
    #[maintains((mut self).inv(*f))]
    #[maintains((mut d).inv(f.num_vars@))]
    #[requires(f.inv())]
    #[requires(cref@ < f.clauses@.len())]
    #[requires(f.clauses@[cref@]@.len() == 1)]
    #[requires(f.clauses@[cref@].inv(f.num_vars@))]
    // unsure which of these is wanted
    //#[ensuresf.clauses@[cref@].sat((^self).assignments))]
    #[ensures(match result {
        Err(_) => true,
        Ok(_) => f.clauses@[cref@]@[0].sat((^self).assignments)})]
    #[requires(long_are_post_unit_inner(self.trail@, *f, self.assignments@))]
    #[ensures(long_are_post_unit_inner((^self).trail@, *f, (^self).assignments@))]
    pub fn learn_unit(&mut self, cref: usize, f: &Formula, d: &mut Decisions) -> Result<(), ()> {
        if self.decision_level() > 0 {
            self.backtrack_to(0, f, d);
        }
        // I have to do a proof here that it is unset after ->
        // will need another requires
        if f[cref][0].lit_set(&self.assignments) {
            return Err(()); // UGLY Runtime check
        }
        self.enq_assignment(Step { lit: f[cref][0], decision_level: 0, reason: Reason::Unit(cref) }, f);
        Ok(())
    }

    #[cfg_attr(feature = "trust_trail", trusted)]
    #[maintains((mut self).inv(*f))]
    #[maintains((mut d).inv(f.num_vars@))]
    #[requires(f.inv())]
    // TODO: https://github.com/creusot-rs/creusot/issues/1504
    /*
    #[ensures(match result {
        Some(true) => f.not_satisfiable(),
        _ => true,
    })]
    */
    #[ensures(match result {
        Some(b) => if b { f.not_satisfiable() } else  { true },
        _ => true,
    })]
    pub fn learn_units(&mut self, f: &Formula, d: &mut Decisions) -> Option<bool> {
        let mut i = 0;
        let old_d: Snapshot<&mut Decisions> = snapshot! { d };
        let old_self: Snapshot<&mut Trail> = snapshot! { self };
        #[invariant(self.inv(*f))]
        #[invariant(d.inv(f.num_vars@))]
        while i < f.clauses.len() {
            let clause = &f[i];
            if clause.len() == 1 {
                let lit = clause[0];
                if lit.lit_set(&self.assignments) {
                    if lit.lit_unsat(&self.assignments) {
                        // TODO: As soon as the bijection between trail and assignments is reestablished,
                        // this should come quite easily.
                        use crate::conflict_analysis::resolve_empty_clause;
                        return Some(resolve_empty_clause(f, self, i));
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
