extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::assignments::*;
use crate::lit::*;
use crate::formula::*;
use crate::logic::*;
use crate::clause::*;

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

#[cfg(contracts)]
impl Model for Trail {
    type ModelTy = (Seq<Vec<Lit>>, Seq<(usize, Reason)>);

    #[logic]
    fn model(self) -> Self::ModelTy {
        (self.trail.model(), self.vardata.model())
    }
}

#[predicate]
pub fn clause_post_with_regards_to_lit(c: Clause, a: Assignments, lit: Lit) -> bool {
    pearlite! {
        c.post_unit(a) &&
        exists<i: Int> 0 <= i && i < (@c).len() &&
            (@c)[i].polarity === lit.polarity &&
            @(@c)[i].idx === @lit.idx &&
            (@c)[i].sat(a) 
    }
}

// unused
#[trusted] // OK
#[logic]
#[requires(c.invariant(@f.num_vars))]
#[requires(a.invariant(f))]
#[requires(c.post_unit(a))]
#[ensures(forall<i: Int> 0 <= i && i < (@c).len() ==> !(@c)[i].unset(a))]
fn lemma_post_unit_no_unset(c: Clause, a: Assignments, f: Formula) {}

#[trusted] // OK
#[logic]
#[requires(a.invariant(f))]
#[requires(f.invariant())]
#[requires(lit.invariant(@f.num_vars))]
#[requires(unset((@a)[@lit.idx]))]
#[ensures(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    (@f.clauses)[i].post_unit_inner(@a) ==> 
    (@f.clauses)[i].post_unit_inner((@a).set(@lit.idx, 1u8))
)]
#[ensures(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    (@f.clauses)[i].post_unit_inner(@a) ==> 
    (@f.clauses)[i].post_unit_inner((@a).set(@lit.idx, 0u8))
)]
fn lemma_assign_maintains_post_for_each(f: Formula, a: Assignments, lit: Lit) {}

#[trusted] // OK
#[logic]
#[requires(a.invariant(f))]
#[requires(f.invariant())]
#[requires(vardata_invariant(v, @f.num_vars))]
#[requires(crefs_in_range(v, f))]
#[requires(lit.invariant(@f.num_vars))]
#[requires(unset((@a)[@lit.idx]))]
#[requires(long_are_post_unit_inner(v, f, @a))]
#[requires(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    (@f.clauses)[i].post_unit_inner(@a) ==> 
    (@f.clauses)[i].post_unit_inner((@a).set(@lit.idx, 1u8))
)]
#[requires(forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
    (@f.clauses)[i].post_unit_inner(@a) ==> 
    (@f.clauses)[i].post_unit_inner((@a).set(@lit.idx, 0u8)) 
)]
#[ensures(long_are_post_unit_inner(v, f, (@a).set(@lit.idx, 1u8)))]
#[ensures(long_are_post_unit_inner(v, f, (@a).set(@lit.idx, 0u8)))]
fn lemma_assign_maintains_for_each_to_post(v: Seq<(usize, Reason)>, f: Formula, a: Assignments, lit: Lit) {}

#[trusted] // OK
#[logic]
#[requires(a.invariant(f))]
#[requires(f.invariant())]
#[requires(vardata_invariant(v, @f.num_vars))]
#[requires(crefs_in_range(v, f))]
#[requires(lit.invariant(@f.num_vars))]
#[requires(unset((@a)[@lit.idx]))]
#[requires(long_are_post_unit_inner(v, f, @a))]
#[ensures(long_are_post_unit_inner(v, f, (@a).set(@lit.idx, 1u8)))]
#[ensures(long_are_post_unit_inner(v, f, (@a).set(@lit.idx, 0u8)))]
pub fn lemma_assign_maintains_long_are_post_unit(v: Seq<(usize, Reason)>, f: Formula, a: Assignments, lit: Lit) {
    lemma_assign_maintains_post_for_each(f, a, lit);
    lemma_assign_maintains_for_each_to_post(v, f, a, lit);
}

#[predicate]
pub fn clause_post_with_regards_to(c: Clause, a: Assignments, j: Int) -> bool {
    pearlite! {
        c.post_unit(a) &&
        exists<i: Int> 0 <= i && i < (@c).len() &&
            @(@c)[i].idx === j &&
            (@c)[i].sat(a) 
    }
}

#[predicate]
pub fn clause_post_with_regards_to_inner(c: Clause, a: Seq<AssignedState>, j: Int) -> bool {
    pearlite! {
        c.post_unit_inner(a) &&
        exists<i: Int> 0 <= i && i < (@c).len() &&
            @(@c)[i].idx === j &&
            (@c)[i].sat_inner(a) 
    }
}

#[predicate]
pub fn long_are_no_unset(vardata: Seq<(usize, Reason)>, f: Formula, a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < vardata.len() ==> match
        vardata[j].1 { 
            Reason::Long(k) => { (@f.clauses)[@k].no_unset_inner(a) },
                _ => true,
            }
    }
}

#[predicate]
pub fn long_are_post_unit_inner(vardata: Seq<(usize, Reason)>, f: Formula, a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < vardata.len() ==> match
        vardata[j].1 { 
            Reason::Long(k) => { clause_post_with_regards_to_inner((@f.clauses)[@k], a, j) },
                _ => true,
            }
    }
}


#[predicate]
pub fn long_are_post_unit(vardata: Seq<(usize, Reason)>, f: Formula, a: Assignments) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < vardata.len() ==> match
        vardata[j].1 { 
            Reason::Long(k) => { clause_post_with_regards_to((@f.clauses)[@k], a, j) },
                _ => true,
            }
    }
}

#[predicate]
pub fn vardata_invariant(vardata: Seq<(usize, Reason)>, n: Int) -> bool {
        pearlite! { vardata.len() === n }
}

#[predicate]
// All the long clauses carry a cref which is inside the formula
pub fn crefs_in_range(vardata: Seq<(usize, Reason)>, f: Formula) -> bool {
    pearlite! {
        forall<j: Int> 0 <= j && j < vardata.len() ==>
            match vardata[j].1 {
                Reason::Long(k) => 0 <= @k && @k < (@f.clauses).len(),
                _ => true,
            }
    }
}

#[predicate]
// All the indexes in trail are less than f.num_vars
pub fn trail_invariant(trail: Seq<Vec<Lit>>, f: Formula) -> bool {
    pearlite! { 
        forall<i: Int> 0 <= i && i < trail.len() ==> (
        forall<j: Int> 0 <= j && j < (@trail[i]).len() ==>
            0 <= @(@trail[i])[j].idx && @(@trail[i])[j].idx < @f.num_vars )
        }
}

#[predicate]
pub fn trail_invariant_full(trail: Seq<Vec<Lit>>, vardata: Seq<(usize, Reason)>, f: Formula) -> bool {
    pearlite! { 
        trail_invariant(trail, f) && vardata_invariant(vardata, @f.num_vars) && crefs_in_range(vardata, f)
    }
}

#[predicate]
pub fn trail_invariant_full_no_sep(trail: (Seq<Vec<Lit>>, Seq<(usize, Reason)>), f: Formula) -> bool {
    trail_invariant_full(trail.0, trail.1, f)
}

impl Trail {
    #[predicate]
    // Just the length bound atm
    pub fn vardata_invariant(self, n: Int) -> bool {
        pearlite! {
            vardata_invariant(@self.vardata, n)
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
            trail_invariant(@self.trail, f)
        }
    }

    #[predicate]
    // All the long clauses carry a cref which is inside the formula
    pub fn crefs_in_range(self, f: Formula) -> bool {
        pearlite! {
            crefs_in_range(@self.vardata, f)
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

    // We can make vardata nonwiping by having the predicate be reliant on assignments:
    // if entry is set => post_unit
    // if unset => true
    #[predicate]
    pub fn long_are_post_unit(self, f: Formula, a: Assignments) -> bool {
        pearlite! {
            long_are_post_unit(@self.vardata, f, a)
        }
    }

    #[predicate]
    #[ensures(result === (long_are_post_unit(@self.vardata, f, a)))]
    pub fn trail_sem_invariant(self, f: Formula, a: Assignments) -> bool {
        pearlite! {
            long_are_post_unit(@self.vardata, f, a)
            //self.long_are_post_unit(f, a)
        }
    }

    #[predicate]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! { 
            trail_invariant_full(@self.trail, @self.vardata, f)

            /*
            self.vardata_invariant(@f.num_vars) &&             */
        }
    }
}

impl Trail {
    #[trusted] // OK
    #[requires(self.trail_sem_invariant(*_f, *_a))]
    #[ensures((^self).trail_sem_invariant(*_f, *_a))]
    #[requires(self.invariant(*_f))]
    #[requires(0 <= @lit.idx && @lit.idx < @_f.num_vars)]
    #[requires((@self.trail).len() > 0)]
    #[requires(match reason {
        Reason::Undefined => true,
        Reason::Decision => true,
        Reason::Unit => true,
        Reason::Long(k) => 0 <= @k && @k < (@_f.clauses).len() &&
        clause_post_with_regards_to_lit((@_f.clauses)[@k], *_a, lit)
        /*
        (@_f.clauses)[@k].post_unit(*_a) &&
            exists<i: Int> 0 <= i && i < (@(@_f.clauses)[@k]).len() &&
                (@(@_f.clauses)[@k])[i].polarity === lit.polarity &&
                @(@(@_f.clauses)[@k])[i].idx === @lit.idx &&
                (@(@_f.clauses)[@k])[i].sat(*_a)  
                */
    })]
    #[ensures((^self).invariant(*_f))]
    #[ensures((@(^self).trail).len() === (@self.trail).len())]
    #[ensures((@(^self).vardata).len() === (@self.vardata).len())]
    #[ensures((@(@(^self).trail)[(@self.trail).len()-1]) === (@(@self.trail)[(@self.trail).len()-1]).push(lit))]
    #[ensures(forall<i: Int> 0 <= i && i < (@self.trail).len() - 1 ==>
        (@self.trail)[i] === (@(^self).trail)[i])]
    #[ensures(forall<i: Int> 0 <= i && i < (@self.vardata).len() && i != @lit.idx ==>
        (@self.vardata)[i] === (@(^self).vardata)[i])]
    #[ensures(@(@(^self).vardata)[@lit.idx].0 === (@self.trail).len()-1)]
    #[ensures((@(^self).vardata)[@lit.idx].1 === reason)]
    pub fn enq_assignment(&mut self, lit: Lit, reason: Reason, _f: &Formula, _a: &Assignments) {
        let dlevel = self.trail.len() - 1;
        self.trail[dlevel].push(lit);
        self.vardata[lit.idx] = (dlevel, reason);
    }

    #[trusted] // OK
    #[ensures(result.invariant(*f))]
    #[ensures((@result.trail).len() === 1)]
    #[ensures(result.trail_sem_invariant(*f, *_a))]
    pub fn new(f: &Formula, _a: &Assignments) -> Trail {
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
    #[ensures(@self.vardata === @(^self).vardata)]
    #[ensures(forall<i: Int> 0 <= i && i < (@self.trail).len() ==>
        (@self.trail)[i] === (@(^self).trail)[i])]
    #[ensures((@(^self).trail).len() === (@self.trail).len() + 1)]
    #[ensures((@(@(^self).trail)[(@self.trail).len()]).len() === 0)]
    pub fn add_level(&mut self, _f: &Formula) {
        self.trail.push(Vec::new());
    }
}