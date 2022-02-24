extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::formula::*;
use crate::lit::*;
use crate::trail::*;

// OK using u32s temporarily, should be u8. Gotta add u8s to Creusot
//#[derive(Eq, PartialEq)]
pub struct Assignments(pub Vec<u8>);

impl Model for Assignments {
    type ModelTy = Seq<u8>;

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
    #[trusted] // OK
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

    #[trusted] // OK
    #[ensures(result.invariant(@f.num_vars))]
    pub fn init_assignments(f: &Formula) -> Assignments {
        let assign = vec::from_elem(2u8, f.num_vars);
        Assignments(assign)
    }

    #[trusted] // OK
    #[ensures(match result {
        Some(lit) => @(@self)[@lit.idx] >= 2,
        None => forall<i : Int> 0 <= i && i < (@self).len() ==> 
                !(@(@self)[i] >= 2)
    })]
    #[ensures(match result {
        Some(lit) => 0 <= @lit.idx && @lit.idx < (@self).len(),
        None => true
    })]
    pub fn find_unassigned_lit(&self) -> Option<Lit> {
        let mut i: usize = 0;
        #[invariant(i_less, 0 <= @i && @i <= (@self).len())]
        #[invariant(not_unset, forall<j: Int> 0 <= j && j < @i ==>
            @(@self)[j] < 2)]
        while i < self.0.len() {
            if self.0[i] >= 2 {
                return Some(Lit{ idx: i, polarity: true }); // TODO change
            }
            i += 1;
        }
        None
    }   

    //#[trusted] // OK
    //#[requires(trail.trail_entries_are_assigned(*self))] // Gonna need this at some point
    #[requires(@level <= (@trail.trail).len())]
    #[requires(trail.invariant(*_f))]
    #[requires(self.invariant(@_f.num_vars))]
    #[requires(@level > 0)]
    #[ensures((^trail).invariant(*_f))]
    #[ensures((^self).invariant(@_f.num_vars))]
    #[ensures((@(^trail).vardata) === (@trail.vardata))]
    #[ensures((@(^trail).trail).len() === @level)]
    #[ensures(forall<j: Int> 0 <= j && j < @level ==> 
        (@(^trail).trail)[j] === (@trail.trail)[j])] // new
    pub fn cancel_until(&mut self, trail: &mut Trail, level: usize, _f: &Formula) {
        let mut i: usize = trail.trail.len();
        let old_self = Ghost::record(&self);
        let old_trail = Ghost::record(&trail);
        #[invariant(i_bound, @i >= @level)]
        #[invariant(i_is_trail_len, @i === (@trail.trail).len())]
        #[invariant(trail_len, (@trail.trail).len() > 0)]
        #[invariant(maintains_trail_inv, trail.invariant(*_f))]
        #[invariant(vardata_ok, (@trail.vardata) === @(@old_trail).vardata)]
        #[invariant(trail_ok, forall<j: Int> 0 <= j && j < @i ==>
            (@(@old_trail).trail)[j] === (@trail.trail)[j])]
        #[invariant(maintains_ass_inv, self.invariant((@trail.vardata).len()))]
        #[invariant(intact, ^self === ^@old_self)]
        #[invariant(intact_trail, ^trail === ^@old_trail)]
        //#[invariant(assigned, trail.trail_entries_are_assigned(*self))]
        while i > level {
            let decisions = trail.trail.pop();
            match decisions {
                Some(decisions) => {
                    let mut j: usize = 0;
                    //#[invariant(assigned2, trail.trail_entries_are_assigned(*self))]
                    #[invariant(maintains_trail_inv2, trail.invariant(*_f))]
                    #[invariant(maintains_ass_inv2, self.invariant((@trail.vardata).len()))]
                    #[invariant(same_len_trail, (@trail.vardata).len() === (@(@old_trail).vardata).len())]
                    #[invariant(intact_self2, ^self === ^@old_self)]
                    #[invariant(intact_trail2, ^trail === ^@old_trail)]
                    #[invariant(i_is_trail_len2, @i - 1 === (@trail.trail).len())]
                    #[invariant(j_less, 0 <= @j && @j <= (@decisions).len())]
                    /*
                    #[invariant(assigned_dec, forall<k: Int> @j <= k && k < (@decisions).len() ==>
                        @(@self)[@(@decisions)[k].idx] < 2)]
                    #[invariant(assigned_dec2, forall<k: Int> 0 <= k && k < @j ==>
                        @(@self)[@(@decisions)[k].idx] >= 2)]
                        */
                    while j < decisions.len() {
                        let lit = decisions[j];
                        //trail.vardata[lit.idx] = (0, Reason::Undefined); // Comment out this to make it pass // No need to wipe it
                        //self.0[lit.idx] += 2; // TODO
                        self.0[lit.idx] = 2; // I'll do the phase saving later lol
                        j += 1;
                    }
                }
                None => {
                    panic!();
                }
            }
            i -= 1;
        }
    }
}