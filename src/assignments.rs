extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::{
    clause::*,
    decision::*,
    formula::*,
    lit::*,
    trail::*,
    //trail::{NTrail, Step},
};

#[cfg(contracts)]
use crate::logic::{
    logic::*,
    logic_assignments::*,
    logic_clause::*,
    logic_trail::{trail_invariant, long_are_post_unit_inner_new},
};

pub type AssignedState = u8;
pub struct Assignments(pub Vec<AssignedState>, pub usize);


impl Assignments {
    #[trusted] // TODO
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.0.len()
    }
    /*
    // Not used
    #[trusted] // Broken atm, fix later
    #[ensures(forall<i: Int> 0 <= i && i < (@self).len() ==> (@self)[i] === (@result)[i])]
    #[ensures((@self).len() === (@result).len())]
    #[ensures(@result.1 === @self.1)]
    #[ensures(@*self == @result)]
    pub fn clone(&self) -> Self {
        let mut out = Vec::new();
        let mut i: usize = 0;
        #[invariant(loop_invariant, 0 <= @i && @i <= (@self).len())]
        #[invariant(equality, forall<j: Int> 0 <= j && j < @i ==> (@out)[j] === (@self)[j])]
        #[invariant(len, (@out).len() === @i)]
        while i < self.0.len() {
            let curr = self.0[i];
            //out.push(curr.clone());
            out.push(curr);
            i += 1;
        }
        Assignments(out, self.1)
    }
    */

    /* Starlit:
impl PartialAssignment {
    /// Assigns `true` to the given literal.
    ///
    /// A variable can be assigned `false` by assigning `true` to the negated literal.
    #[inline(always)]
    pub fn assign(&mut self, lit: Lit) {
        self.assigned[lit.index()] = lit.is_positive() as u8
    }

    /// Removes any assigned value from a variable.
    #[inline(always)]
    pub fn unassign(&mut self, var: Var) {
        self.assigned[var.index()] = 2
    }

    /// Returns `true` if the literal is assigned `true`.
    #[inline(always)]
    pub fn is_true(&self, lit: Lit) -> bool {
        self.assigned[lit.index()] == lit.is_positive() as u8
    }

    /// Returns `true` if the literal is assigned `false`.
    #[inline(always)]
    pub fn is_false(&self, lit: Lit) -> bool {
        self.assigned[lit.index()] == lit.is_negative() as u8
    }

    /// Returns `true` if the literal is assigned.
    #[inline(always)]
    pub fn is_assigned(&self, var: Var) -> bool {
        self.assigned[var.index()] != 2
    }
}

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
        self.0[lit.idx] = lit.polarity as u8;
        /*
        if lit.polarity {
            self.0[lit.idx] = 1;
            //proof_assert!(@self === (@@old_self).set(@lit.idx, 1u8));
        } else {
            self.0[lit.idx] = 0;
            //proof_assert!(@self === (@@old_self).set(@lit.idx, 0u8));
        }
        */
        proof_assert!((lemma_assign_maintains_long_are_post_unit(@_t.vardata, *_f, *@old_self, lit));true);
        proof_assert!(^@old_self === ^self);

        proof_assert!(long_are_post_unit_inner(@_t.vardata, *_f, @self));
        //self.0[l.idx] = l.polarity as u8;
    }
    */

    #[inline(always)]
    #[cfg_attr(contracts, trusted)]
    /*
    #[trusted] // Post failing(as expected)
    #[requires(lit.invariant(@_f.num_vars))]
    #[requires(_f.invariant())]
    // TODO:
    #[requires(trail_invariant(@_t, *_f))] // #[requires(_t.invariant(*_f))]
    //#[requires(_t.trail_sem_invariant(*_f, *self))]

    #[requires(self.invariant(*_f))]//#[requires(a.invariant(f))]
    #[requires(unset((@self)[@lit.idx]))] // Added, will break stuff further up
    #[ensures((^self).invariant(*_f))]
    #[ensures(@(@^self)[@lit.idx] === 1 || @(@^self)[@lit.idx] === 0)] // Is this needed?
    #[ensures((@^self).len() === (@self).len())]
    /*
    #[ensures(_t.trail_sem_invariant(*_f, ^self))]
    */
    #[requires(long_are_post_unit_inner_new(@_t, *_f, @self))]
    #[ensures(long_are_post_unit_inner_new(@_t, *_f, @^self))]
    #[ensures((forall<j : Int> 0 <= j && j < (@self).len() &&
        j != @lit.idx ==> (@*self)[j] === (@^self)[j]))]
    #[ensures(lit.sat(^self))]
    */
    pub fn set_assignment_new(&mut self, lit: Lit, _f: &Formula, _t: &Vec<Step>) {
        /*
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
        */

        // zzTODOzz 
       //self.0[lit.idx] = lit.polarity as u8;
        if lit.polarity {
            self.0[lit.idx] = 1;
            //proof_assert!(@self === (@@old_self).set(@lit.idx, 1u8));
        } else {
            self.0[lit.idx] = 0;
            //proof_assert!(@self === (@@old_self).set(@lit.idx, 0u8));
        }
       /*
        */
        /*
        proof_assert!((lemma_assign_maintains_long_are_post_unit(@_t.vardata, *_f, *@old_self, lit));true);
        proof_assert!(^@old_self === ^self);

        proof_assert!(long_are_post_unit_inner(@_t.vardata, *_f, @self));
        */
        //self.0[l.idx] = l.polarity as u8;
    }

    #[trusted] // OK
    #[requires(f.invariant())]
    #[ensures(result.invariant(*f))]
    pub fn new(f: &Formula) -> Self {
        //Assignments(vec::from_elem(2u8, f.num_vars))
        let mut assign: Vec<AssignedState> = Vec::new();
        let mut i: usize = 0;
        #[invariant(loop_invariant, 0 <= @i && @i <= @f.num_vars)]
        #[invariant(length_invariant, (@assign).len() === @i)]
        while i < f.num_vars {
            assign.push(2);
            i += 1
        }
        Assignments(assign, 0)
    }

    #[trusted] // OK
    //#[requires(!self.complete())]
    #[requires(self.invariant(*_f))]
    #[requires(d.invariant((@self).len()))]
    #[ensures(match result {
        Some(res) => @res < (@self).len() && unset((@self)[@res]),
        None => self.complete(),
    }
    )]
    #[ensures(@self === @^self)]
    #[ensures((^self).invariant(*_f))]
    pub fn find_unassigned(&mut self, d: &Decisions, _f: &Formula) -> Option<usize> {
        let mut i: usize = self.1;
        #[invariant(i_bound, @i <= (@d.lit_order).len())]
        while i < d.lit_order.len() {
            let curr = self.0[d.lit_order[i]];
            if curr >= 2 {
                //let b = curr != 2;
                self.1 = i + 1;
                //return Some(Lit{ idx: d.lit_order[i], polarity: b });
                return Some(d.lit_order[i]);
            }
            i += 1;
        }
        // Strictly speaking this is an unecessary runtime check, but it only gets run at most once and it
        // greatly simplifies the proof.
        i = 0;
        #[invariant(prev, forall<j: Int> 0 <= j && j < @i ==> !unset((@self)[j]))]
        while i < self.0.len() {
            if self.0[i] >= 2 {
                return Some(i);
            }
            i += 1;
        }
        None
    }

    /*
    #[trusted] // --TODO--
    #[requires(long_are_post_unit(@vardata, *_f, *self))]
    #[requires(vars_in_range_inner(@curr_level, @_f.num_vars))]
    #[requires(trail_invariant_full(@trail, @vardata, *_f))]
    #[requires(self.invariant(*_f))]
    // Okay we need to ensure that afterwards order is ensured
    //#[requires(trail.trail_entries_are_assigned(*a))]
    //#[ensures((^trail).trail_entries_are_assigned(^a))]
    #[ensures((@vardata).len() === (@^vardata).len())]
    #[ensures((^self).invariant(*_f))]
    /*
    #[ensures((@(^trail).vardata) === (@trail.vardata))]
    #[ensures((@(^trail).trail).len() === @level)]
    #[ensures(forall<j: Int> 0 <= j && j < @level ==>
        (@(^trail).trail)[j] === (@trail.trail)[j])] // new
        */
        /*
    #[ensures((^trail).assignments_invariant(^self))]
    #[ensures(forall<j: Int> @level <= j && j < (@trail.trail).len() ==>
        forall<i: Int> 0 <= i && i < (@(@trail.trail)[j]).len() ==>
            @(@(^self))[@(@(@trail.trail)[j])[i].idx] === 2)]
        //(@(^trail).trail)[j].assigned(^self))]
        */
    //#[requires(trail.trail_sem_invariant(*_f, *self))] // added
    //#[ensures((^trail).trail_sem_invariant(*_f, ^self))] // added
    #[ensures(trail_invariant_full(@trail, @^vardata, *_f))]
    #[ensures(long_are_post_unit(@^vardata, *_f, ^self))]
    pub fn wipe_level(&mut self, trail: &Vec<Vec<Lit>>, vardata: &mut Vec<(usize, Reason)>, curr_level: Vec<Lit>, _f: &Formula) {
        let mut j: usize = 0;
        let curr_level_len: usize = curr_level.len();
        if curr_level_len == 0 { return; }
        let old_vardata = Ghost::record(&vardata);
        let old_self = Ghost::record(&self);
        //#[invariant(assigned2, trail.trail_entries_are_assigned(*self))]
        #[invariant(maintains_ass_inv2, self.invariant(*_f))]
        #[invariant(same_len_trail, (@vardata).len() === (@@old_vardata).len())]
        #[invariant(same_len_ass, (@self).len() === (@@old_self).len())]
        #[invariant(intact_self2, ^self === ^@old_self)]
        #[invariant(intact_vardata, ^vardata === ^@old_vardata)]
        #[invariant(crefs, crefs_in_range(@vardata, *_f))]
        #[invariant(j_less, 0 <= @j && @j <= (@curr_level).len())]
        #[invariant(wiped, forall<k: Int> 0 <= k && k < @j ==>
            (@vardata)[@(@curr_level)[@curr_level_len - k - 1].idx] === (0usize, Reason::Undefined))]
        // Is this invariant even provable? It might be if we count downwards.
        // Also might be possible if we prove that the removal of an entire decision level
        // results in long_post. Still a whole proof about the semantics of the trail,
        // and maybe the full wipe/search restart is easier(as long as the invariant
        // that everything on d0 is units is enforced).
        // Okay for this invariant to work we need to prove that if
        // we were post_unit before, and then added something, then we are post_unit after
        // and then prove that the same applies the opposite direction as well.
        // Need to have a proof that the trail is directly mapped to assignments + vardata
        #[invariant(maintains_post_unit, long_are_post_unit(@vardata, *_f, *self))] // need a lemma // only thing missing
        while j < curr_level_len {
            let lit = curr_level[curr_level_len - j - 1];
            vardata[lit.idx] = (0, Reason::Undefined); // Wiping is not needed for correctness
            proof_assert!(long_are_post_unit(@vardata, *_f, *self));
            proof_assert!((@vardata)[@(@curr_level)[@curr_level_len - @j - 1].idx] === (0usize, Reason::Undefined));
            //self.0[lit.idx] += 2; // zzTODOzz
            if self.0[lit.idx] == 0 {
                self.0[lit.idx] = 2;
            } else {
                self.0[lit.idx] = 3;
            }
            j += 1;
        }
    }

    #[trusted] // OK // Level fails later, though
    //#[requires(trail.trail_entries_are_assigned(*self))] // Gonna need this at some point
        /*
    #[ensures((^trail).assignments_invariant(^self))]
    #[ensures(forall<j: Int> @level <= j && j < (@trail.trail).len() ==>
        forall<i: Int> 0 <= i && i < (@(@trail.trail)[j]).len() ==>
            @(@(^self))[@(@(@trail.trail)[j])[i].idx] === 2)]
        //(@(^trail).trail)[j].assigned(^self))]
        */
    #[requires(@level <= (@trail.trail).len())]
    #[requires(trail.invariant(*_f))]
    #[requires(self.invariant(*_f))]
    #[requires(@level > 0)]
    #[requires(trail.trail_entries_are_assigned(*self))]
    #[ensures((^trail).trail_entries_are_assigned(^self))]
    #[ensures((^trail).invariant(*_f))]
    #[ensures((^self).invariant(*_f))]
    #[ensures((@(^trail).trail).len() === @level)]
    #[ensures(forall<j: Int> 0 <= j && j < @level ==>
        (@(^trail).trail)[j] === (@trail.trail)[j])] // new
    #[requires(trail.trail_sem_invariant(*_f, *self))] // added
    #[ensures((^trail).trail_sem_invariant(*_f, ^self))] // added
    pub fn cancel_until(&mut self, trail: &mut Trail, level: usize, _f: &Formula) {
        let mut i: usize = trail.trail.len();
        let old_self = Ghost::record(&self);
        let old_trail = Ghost::record(&trail);
        #[invariant(i_bound, @i >= @level)]
        #[invariant(i_is_trail_len, @i === (@trail.trail).len())]
        #[invariant(trail_len, (@trail.trail).len() > 0)]
        #[invariant(maintains_trail_inv, trail.invariant(*_f))]
        //#[invariant(vardata_ok, (@trail.vardata) === @(@old_trail).vardata)]
        #[invariant(trail_ok, forall<j: Int> 0 <= j && j < @i ==>
            (@(@old_trail).trail)[j] === (@trail.trail)[j])]
        #[invariant(maintains_ass_inv, self.invariant(*_f))]
        #[invariant(intact, ^self === ^@old_self)]
        #[invariant(intact_trail, ^trail === ^@old_trail)]
        //#[invariant(assigned, trail.trail_entries_are_assigned(*self))]
        #[invariant(maintains_sem_inv_o, trail.trail_sem_invariant(*_f, *self))]
        while i > level {
            let old_t = Ghost::record(&trail);
            let curr_level = trail.trail.pop();
            match curr_level {
                Some(curr_level) => {
                    self.wipe_level(&trail.trail, &mut trail.vardata, curr_level, _f);
                }
                None => {
                    panic!();
                }
            }
            i -= 1;
        }
        self.1 = 0; // ADDED
    }
    */

    /*
    #[trusted] // OK
    #[requires(self.invariant(@_f.num_vars))]
    //#[requires((@self)[@lit.idx] >= 2)] // This is a correctness req
    #[ensures((^self).invariant(@_f.num_vars))]
    #[ensures(@(@^self)[@lit.idx] === 1 || @(@^self)[@lit.idx] === 0)]
    #[ensures((forall<j : Int> 0 <= j && j < (@self).len() &&
    j != @lit.idx ==> (@*self)[j] === (@^self)[j]))]
    #[requires(0 <= @lit.idx && @lit.idx < (@self).len())]
    #[ensures(
        match lit.polarity {
            true => @(@^self)[@lit.idx] === 1,
            false => @(@^self)[@lit.idx] === 0,
        }
    )]
    //#[ensures(self.compatible(^self))]
    #[ensures((forall<j : Int> 0 <= j && j < (@self).len() &&
        j != @lit.idx ==> (@*self)[j] === (@^self)[j]))]
    #[ensures((@^self).len() === (@self).len())]
    pub fn set_assignment(&mut self, lit: Lit, _f: &Formula) {
        /*
        if !self.0[l.idx].is_none() {
            panic!("Assignment already set.");
        }
        */
        if lit.polarity {
            self.0[lit.idx] = 1;
        } else {
            self.0[lit.idx] = 0;
        }
        //self.0[lit.idx] = lit.polarity as u8;
        //self.0[lit.idx] = Some(lit.polarity);
    }
    */
}
