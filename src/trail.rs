extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::assignments::*;
use crate::lit::*;
use crate::formula::*;
use crate::logic::*;

//#[derive(Debug, Clone, PartialEq, Eq)]
#[derive(Copy, Clone)]
pub enum Reason {
    Undefined,
    Decision,
    Unit,
    Long(usize),
}

impl Default for Reason {
    fn default() -> Self { Reason::Undefined }
}

//#[derive(Debug)]
pub struct Trail {
    pub trail: Vec<Vec<Lit>>,
    pub vardata: Vec<(usize, Reason)>,
}

impl Trail {
    #[predicate]
    // Just the length bound atm
    pub fn vardata_invariant(self, n: Int) -> bool {
        pearlite! { (@self.vardata).len() === n 
            // This used to be correct, but isnt after we stopped wiping
            //&& 
            //forall<i: Int> 0 <= i && i < (@self.vardata).len() ==>
        //@(@self.vardata)[i].0 < (@self.trail).len()
        }
    }

    #[predicate]
    // All the indexes in trail are less than f.num_vars
    pub fn trail_invariant(self, f: Formula) -> bool {
        pearlite! { 
            forall<i: Int> 0 <= i && i < (@self.trail).len() ==> (
            forall<j: Int> 0 <= j && j < (@(@self.trail)[i]).len() ==>
                0 <= @(@(@self.trail)[i])[j].idx && @(@(@self.trail)[i])[j].idx < @f.num_vars )
            }
    }

    #[predicate]
    // All the long clauses carry a cref which is inside the formula
    pub fn crefs_in_range(self, f: Formula) -> bool {
        pearlite! {
            forall<j: Int> 0 <= j && j < (@self.vardata).len() ==>
            match (@self.vardata)[j].1 {
                Reason::Long(k) => 0 <= @k && @k < (@f.clauses).len(),
                _ => true,
            }
        }
    }

    #[predicate]
    pub fn old_trail_entries_are_assigned(self, a: Assignments) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self.trail).len() ==>
            forall<j: Int> 0 <= j && j < (@(@self.trail)[i]).len() ==>
                @(@a)[@(@(@self.trail)[i])[j].idx] < 2
        }
    }

    #[predicate]
    pub fn trail_entries_are_assigned(self, a: Assignments) -> bool {
        pearlite! {
            forall<j: Int> 0 <= j && j < (@self.trail).len() ==>
                forall<k: Int> 0 <= k && k < (@(@self.trail)[j]).len() ==>
                    (@a)[@(@(@self.trail)[j])[k].idx] === bool_to_assignedstate((@(@self.trail)[j])[k].polarity)
        }
    }

    #[predicate]
    pub fn unassigned_not_in_trail(self, a: Assignments) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@a).len() ==>
                @(@a)[i] >= 2 ==>
                forall<j: Int> 0 <= j && j < (@self.trail).len() ==>
                    forall<k: Int> 0 <= k && k < (@(@self.trail)[j]).len() ==>
                        !(@(@(@self.trail)[j])[k].idx === i)
        }
    }

    #[predicate]
    pub fn assignments_invariant(self, a: Assignments) -> bool {
        pearlite! {
            self.trail_entries_are_assigned(a) &&
            self.unassigned_not_in_trail(a)
        }
    }

    #[predicate]
    pub fn long_are_post_unit(self, f: Formula, a: Assignments) -> bool {
        pearlite! {
            forall<j: Int> 0 <= j && j < (@self.vardata).len() ==> match
            (@self.vardata)[j].1 { 
                Reason::Long(k) => {(@f.clauses)[@k].post_unit(a) &&
                exists<i: Int> 0 <= i && i < (@(@f.clauses)[@k]).len() &&
                    @(@(@f.clauses)[@k])[i].idx === j &&
                    (@(@f.clauses)[@k])[i].sat(a) },
                _ => true,
            }
        }
    }

    // TODO
    #[predicate]
    pub fn trail_sem_invariant(self, f: Formula, a: Assignments) -> bool {
        pearlite! {
            self.long_are_post_unit(f, a)
        }
    }


    #[predicate]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            self.vardata_invariant(@f.num_vars) && self.trail_invariant(f) &&  
            self.crefs_in_range(f)
        }
    }
}

impl Trail {
    #[trusted] // OK
    #[requires(self.invariant(*_f))]
    #[requires(0 <= @lit.idx && @lit.idx < @_f.num_vars)]
    #[requires((@self.trail).len() > 0)]
    #[requires(match reason {
        Reason::Undefined => true,
        Reason::Decision => true,
        Reason::Unit => true,
        Reason::Long(k) => 0 <= @k && @k < (@_f.clauses).len()
    })]
    #[ensures((^self).invariant(*_f))]
    #[ensures((@(^self).trail).len() === (@self.trail).len())]
    #[ensures((@(^self).vardata).len() === (@self.vardata).len())]
    #[ensures((@(@((^self).trail))[(@(self).trail).len()-1]) === (@(@(self.trail))[(@(self).trail).len()-1]).push(lit))]
    #[ensures(forall<i: Int> 0 <= i && i < (@self.trail).len() - 1 ==>
        (@self.trail)[i] === (@(^self).trail)[i])]
    #[ensures(forall<i: Int> 0 <= i && i < (@self.vardata).len() && i != @lit.idx ==>
        (@self.vardata)[i] === (@(^self).vardata)[i])]
    #[ensures(@((@((^self).vardata))[@lit.idx]).0 === (@self.trail).len()-1)]
    #[ensures(((@((^self).vardata))[@lit.idx]).1 === reason)]
    pub fn enq_assignment(&mut self, lit: Lit, reason: Reason, _f: &Formula) {
        let dlevel = self.trail.len() - 1;
        self.trail[dlevel].push(lit);
        self.vardata[lit.idx] = (dlevel, reason);
    }

    #[trusted] // OK
    #[ensures(result.invariant(*f))]
    #[ensures((@result.trail).len() === 1)]
    pub fn new(f: &Formula) -> Trail {
        let mut vardata: Vec<(usize, Reason)> = Vec::new();
        let mut i: usize = 0;
        #[invariant(i_less, @i <= @f.num_vars)]
        #[invariant(len_correct, (@vardata).len() === @i)]
        #[invariant(all_undef, 
            forall<j: Int> 0 <= j && j < @i ==>
            @(@vardata)[j].0 === 0 &&
            (@vardata)[j].1 === Reason::Undefined)]
        while i < f.num_vars {
            vardata.push((0, Reason::Undefined));
            i += 1;
        }
        let mut trail: Vec<Vec<Lit>> = Vec::new();
        trail.push(Vec::new());
        Trail {
            trail: trail,
            vardata: vardata,
        }
    }

    #[trusted] // OK
    #[requires(self.invariant(*_f))]
    #[ensures((^self).invariant(*_f))]
    #[ensures((@self.vardata) === (@(^self).vardata))]
    #[ensures(forall<i: Int> 0 <= i && i < (@self.trail).len() ==>
        (@self.trail)[i] === (@(^self).trail)[i])]
    #[ensures((@(^self).trail).len() === (@self.trail).len() + 1)]
    #[ensures((@(@(^self).trail)[(@self.trail).len()]).len() === 0)]
    pub fn add_level(&mut self, _f: &Formula) {
        self.trail.push(Vec::new());
    }
}