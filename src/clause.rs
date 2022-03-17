extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::lit::*;
use crate::assignments::*;
use crate::formula::*;
use crate::logic::*;

//#[derive(Debug)]
//#[derive(Clone)]
pub struct Clause {
    //pub first: Lit,
    //pub second: Lit,
    pub rest: Vec<Lit>
}

impl Clone for Clause {
    #[trusted]
    #[ensures(result === *self)]
    fn clone(&self) -> Self {
        Clause {
            rest: self.rest.clone()
        }
}
}

#[cfg(contracts)]
impl Model for Clause {
    type ModelTy = Seq<Lit>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        self.rest.model()//.push(self.first)//.push(self.second)
    }
}

#[predicate]
pub fn no_duplicate_indexes_inner(s: Seq<Lit>) -> bool {
    pearlite! {
        forall<j: Int, k: Int> 0 <= j && j < s.len() &&
                0 <= k && k < j ==> !(@s[k].idx === @s[j].idx)
    }
    /*
    pearlite! {
        forall<j: Int, k: Int> 0 <= j && j < s.len() &&
                k != j ==> !(@s[k].idx === @s[j].idx)
    }
    */
}

#[predicate]
pub fn vars_in_range_inner(s: Seq<Lit>, n: Int) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < s.len() ==> 
            s[i].invariant(n)
    }
}

#[predicate]
pub fn equisat_extension_inner(c: Clause, f: (Seq<Clause>, Int)) -> bool {
    pearlite! {
        eventually_sat_complete_no_ass(f) ==> eventually_sat_complete_no_ass((f.0.push(c), f.1))
        //f.eventually_sat_complete_no_ass() ==> eventually_sat_complete_no_ass(f)
    }
}

impl Clause {
    #[predicate]
    pub fn equisat_extension(self, f: Formula) -> bool {
        pearlite! {
            equisat_extension_inner(self, @f)
            //f.eventually_sat_complete_no_ass() ==> eventually_sat_complete_no_ass(f)
        }
    }

    #[predicate]
    pub fn equisat_extension_double(self, f: Formula, f2: Formula) -> bool {
        pearlite! {
            f.invariant() && f2.invariant() &&
            @f.num_vars === @f2.num_vars && 
            //(@f.clauses).push(self) === (@f2.clauses) && // Push doesnt pass
            ((@f.clauses).len() + 1 === (@f2.clauses).len() &&
            (forall<i: Int> 0 <= i && i < (@f.clauses).len() ==> 
            ((@f.clauses)[i]).equals((@f2.clauses)[i])) &&
            (@(@f2.clauses)[(@f2.clauses).len()-1] === @self)) &&
            f.equisat_compatible(f2)
        }

    }


    #[predicate]
    pub fn resolvent_of(self, c: Clause, c2: Clause, k: Int, m: Int) -> bool {
        pearlite! {
            (forall<i: Int> 0 <= i && i < (@c ).len() && i != m ==> (@c )[i].lit_in(self)) &&
            (forall<i: Int> 0 <= i && i < (@c2).len() && i != k ==> (@c2)[i].lit_in(self)) &&
            (forall<i: Int> 0 <= i && i < (@self).len()         ==> (@self)[i].lit_in(c) 
                                                                ||  (@self)[i].lit_in(c2)) &&
            (@c2)[k].is_opp((@c)[m])                 
        }
    }

    #[predicate]
    pub fn resolvent_of_idx(self, c: Clause, c2: Clause, idx: Int) -> bool {
        pearlite! {
            (forall<i: Int> 0 <= i && i < (@c ).len() && @(@c )[i].idx != idx ==> (@c )[i].lit_in(self)) &&
            (forall<i: Int> 0 <= i && i < (@c2).len() && @(@c2)[i].idx != idx ==> (@c2)[i].lit_in(self)) &&
            (forall<i: Int> 0 <= i && i < (@self).len()                       ==> (@self)[i].lit_in(c) 
                                                                              ||  (@self)[i].lit_in(c2)) &&
            (exists<k: Int, m: Int> 0 <= k && k < (@c2).len() && 0 <= m && m < (@c).len() &&
                @(@c)[m].idx === idx && @(@c2)[k].idx === idx && (@c2)[k].is_opp((@c)[m]))
        }
    }

    #[predicate]
    pub fn in_formula(self, f: Formula) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@f.clauses).len() &&
                (@f.clauses)[i] === self
        }
    }

    #[predicate]
    pub fn in_formula_inner(self, f: (Seq<Clause>, Int)) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (f.0).len() &&
                (f.0)[i] === self
        }
    }

    #[predicate]
    pub fn unit_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            self.vars_in_range(a.len()) &&
                !self.sat_inner(a) && 
                    exists<i: Int> 0 <= i && i < (@self).len() &&
                        (@self)[i].unset_inner(a) && 
                            (forall<j: Int> 0 <= j && j < (@self).len() && j != i ==>
                                !(@self)[j].unset_inner(a))
        }
    }
    #[predicate]
    pub fn unit(self, a: Assignments) -> bool {
        pearlite! {
            self.unit_inner(@a)
        }
    }

    #[predicate]
    pub fn unsat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self).len() ==>
                (@self)[i].unsat_inner(a)
        }
    }

    #[predicate]
    pub fn unsat(self, a: Assignments) -> bool {
        pearlite! {
            self.unsat_inner(@a)
        }
    }

    #[predicate]
    pub fn sat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@self).len() &&
                (@self)[i].sat_inner(a)
        }
    }

    #[predicate]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! {
            self.sat_inner(@a)
        }
    }

    #[predicate]
    pub fn unknown(self, a: Assignments) -> bool {
        !self.sat(a) && !self.unsat(a)
    }

    #[predicate]
    pub fn vars_in_range(self, n: Int) -> bool {
        pearlite! {            
            vars_in_range_inner(@self, n)
        }
    }

    #[predicate]
    pub fn no_duplicate_indexes(self) -> bool {
        pearlite! {
            no_duplicate_indexes_inner(@self)
        }
    }

    #[predicate]
    pub fn invariant(self, n: Int) -> bool {
        // Should remove the possibility of empty clauses
        pearlite! { self.vars_in_range(n) && self.no_duplicate_indexes() }
    }

    #[predicate]
    pub fn equals(self, o: Clause) -> bool {
        pearlite! {
            (@self).len() === (@o).len() &&
            forall<j: Int> 0 <= j && j < (@self).len() ==>
                (@self)[j] === (@o)[j]
        }
    }
}

//#[derive(Copy, Clone, Eq)]
pub enum ClauseState {
    Sat,
    Unsat,
    Unit,
    Unknown,
    Err(usize),
}

impl Clause {
    #[inline]
    #[trusted] // TODO
    // Requires a bunch of stuff, TODO
    //#[ensures(result.invariant(@_f.num_vars))]
    //#[ensures((@result).len() >= 2)]
    pub fn clause_from_vec(vec: &std::vec::Vec<Lit>) -> Clause {
        Clause { rest: vec.clone() }
        /*
        Clause {
            first: vec[0],
            second: vec[1],
            rest: vec[2..].to_vec()
        }
        */
    }
    #[trusted] // OK
    #[requires(self.invariant((@a).len()))]
    #[requires(f.invariant())]
    #[requires(a.invariant(*f))]
    #[ensures((result === ClauseState::Sat)     ==> self.sat(*a))]
    #[ensures((result === ClauseState::Unsat)   ==> self.unsat(*a))]
    #[ensures((result === ClauseState::Unit)    ==> self.unit(*a) && !a.complete())]
    #[ensures((result === ClauseState::Unknown) ==> !a.complete())]
    pub fn check_if_unit(&self, a: &Assignments, f: &Formula) -> ClauseState {
        let mut i: usize = 0;
        let mut k: usize = 0;
        let mut unassigned: usize = 0;
        #[invariant(loop_invariant, 0 <= @i && @i <= (@self.rest).len())]
        #[invariant(unass, @unassigned <= 1)] 
        #[invariant(k_is_unass, (@unassigned === 0 || (@self)[@k].unset(*a)))]
        #[invariant(kk, @unassigned > 0 ==> (@self)[@k].unset(*a))]
        #[invariant(not_sat, forall<j: Int> 0 <= j && j < @i ==>
            ((@self)[j].unsat(*a) || ((@self)[j].unset(*a) && @unassigned >= 1)))]
        #[invariant(k_in_bounds, @unassigned === 0 || 0 <= @k && @k < (@self).len())]
        #[invariant(k_only, @unassigned === 1 ==> 
            (forall<j: Int> 0 <= j && j < @i && j != @k ==> !(@self)[j].unset(*a)))]
        #[invariant(k_unset, @unassigned === 0 ==> @k === 0)]
        while i < self.rest.len() {
            let lit = self.rest[i];
            if lit.lit_sat(a) {
                return ClauseState::Sat;
            } else if lit.lit_unset(a) { // Could make two different check_if_unit functions, one for pre_sat_possible and one for after
                if unassigned > 0 {
                    return ClauseState::Unknown;
                }
                k = i;
                unassigned += 1;
            }
            i += 1;
        }
        if unassigned == 1 {
            ClauseState::Unit
        } else {
            ClauseState::Unsat
        }
    }

    #[trusted] // OK
    #[requires(self.unit(*a))]
    #[requires(f.invariant())]
    #[requires(a.invariant(*f))]
    #[ensures(exists<j: Int> 0 <= j && j < (@self).len() && (@self)[j] === result)]
    #[ensures(@result.idx < (@a).len())]
    #[ensures(unset((@a)[@result.idx]))]
    pub fn get_unit(&self, a: &Assignments, f: &Formula) -> Lit {
        let mut i: usize = 0;
        #[invariant(not_unset, forall<j: Int> 0 <= j && j < @i ==> !(@self)[j].unset(*a))]
        while i < self.rest.len() {
            let lit = self.rest[i];
            if lit.lit_unset(a) {
                return lit;
            }
            i += 1;
        }
        panic!();
    }
}