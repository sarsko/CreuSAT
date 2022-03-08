extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::lit::*;
use crate::clause::*;
use crate::logic::*;
use crate::formula::*;
use crate::decision::*;
use crate::trail::*;

pub type AssignedState = u8;

pub struct Assignments(pub Vec<AssignedState>, pub usize);


#[cfg(contracts)]
impl Model for Assignments {
    type ModelTy = Seq<AssignedState>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        self.0.model()
    }
}

#[predicate]
pub fn assignments_equality(a: Assignments, a2: Assignments) -> bool {
    pearlite! {
        (@a).len() === (@a2).len() &&
            forall<i: Int> 0 <= i && i < (@a).len() ==> (@a)[i] === (@a2)[i]
    }
}

#[predicate]
pub fn compatible_inner(a: Seq<AssignedState>, a2: Seq<AssignedState>) -> bool {
    pearlite! {
        a.len() === a2.len() && (forall<i: Int> 0 <= i && i < a.len() ==>
            (unset(a[i]) || a[i] === a2[i]))
    }
}

#[predicate]
pub fn complete_inner(a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < a.len() ==> !unset(a[i])
    }
}

#[predicate]
pub fn compatible_complete_inner(a: Seq<AssignedState>, a2: Seq<AssignedState>) -> bool {
    pearlite! {
        compatible_inner(a, a2) && complete_inner(a2)
    }
}

#[predicate]
pub fn assignments_invariant(a: Seq<AssignedState>, f: Formula) -> bool {
    pearlite! {
        @f.num_vars === a.len()
    }
}
 
// Predicates
impl Assignments { 
    #[predicate]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            @f.num_vars === (@self).len() && @self.1 <= @f.num_vars
        }
    }

    #[predicate]
    pub fn compatible(self, a2: Assignments) -> bool {
        pearlite! { compatible_inner(@self, @a2) }
    }

    #[predicate]
    pub fn complete(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self).len() ==> !unset((@self)[i])
        }
    }

    #[predicate]
    pub fn compatible_complete(self, a2: Assignments) -> bool {
        self.compatible(a2) && a2.complete()
    }
}

impl Assignments {
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

    #[inline]
    #[cfg(not(contracts))]
    pub fn set_assignment(&mut self, l: Lit) {
        /*
        if !self.0[l.idx].is_none() {
            panic!("Assignment already set. Attempting to set {:?}", l);
        }
        */
        //assert!(self.0[l.idx].is_none());
        self.0[l.idx] = l.polarity as u8;
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

    //#[trusted] // OK
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

    //#[trusted] // OK
    #[requires(f.invariant())]
    #[requires(self.invariant(*f))]
    #[requires(0 <= @i && @i < (@f.clauses).len())]
    #[requires(t.invariant(*f))]
    #[requires((@t.trail).len() > 0)]
    #[ensures((@(^t).trail).len() === (@t.trail).len())]
    #[ensures((^t).invariant(*f))]
    #[ensures((^self).invariant(*f))]
    #[ensures((*self).compatible(^self))]
    #[ensures(f.eventually_sat_complete(*self) === f.eventually_sat_complete(^self))] 
    #[ensures((result === ClauseState::Unit)    ==> (@f.clauses)[@i].unit(*self) && !(self).complete())]
    #[ensures((result === ClauseState::Sat)     ==> (@f.clauses)[@i].sat(^self) && @self === @^self)]
    #[ensures((result === ClauseState::Unsat)   ==> (@f.clauses)[@i].unsat(^self) && @self === @^self)]
    #[ensures((result === ClauseState::Unknown) ==> @self === @^self && !(^self).complete())]
    #[ensures((self).complete() ==> *self === ^self && ((result === ClauseState::Unsat) || (result === ClauseState::Sat)))]
    pub fn unit_prop_once(&mut self, i: usize, f: &Formula, t: &mut Trail) -> ClauseState {
        let clause = &f.clauses[i];
        let old_a = Ghost::record(&self);
        proof_assert!(^self === ^@old_a);
        match clause.check_if_unit(self, f) {
            ClauseState::Unit => { 
                // I tried both to make ClauseState::Unit contain a usize and to return a tuple, but
                // both were slower than getting it after. Kind of makes sense since unit clauses are
                // rare and we on average have to traverse n/2 lits to find the unit lit. If I make formula
                // mutable, then I can swap to index 0 and skip the call to clause.get_unit()
                let lit = clause.get_unit(self, f);
                proof_assert!(clause.invariant((@self).len()));
                proof_assert!(lemma_unit_wrong_polarity_unsat_formula(*clause, *f, @self, @lit.idx, bool_to_assignedstate(lit.polarity)); true);
                proof_assert!(forall<j: Int> 0 <= j && j < (@clause).len() && !(@(@clause)[j].idx === @lit.idx) ==> !((@clause)[j].unset(*self)));
                proof_assert!(lemma_unit_forces(*clause, *f, @self, @lit.idx, bool_to_assignedstate(lit.polarity)); true);
                if lit.polarity {
                    self.0[lit.idx] = 1;
                } else {
                    self.0[lit.idx] = 0;    
                }
                t.enq_assignment(lit, Reason::Unit, f);
                proof_assert!(@^self == (@*@old_a).set(@lit.idx, bool_to_assignedstate(lit.polarity)));
                proof_assert!(lemma_extension_sat_base_sat(*f, @@old_a, @lit.idx, bool_to_assignedstate(lit.polarity)); true);
                proof_assert!(lemma_extensions_unsat_base_unsat(@@old_a, @lit.idx, *f); true);
                proof_assert!(^self === ^@old_a);
                return ClauseState::Unit;
            },
            o => return o
        }
    }

    #[requires(f.invariant())]
    #[requires(self.invariant(*f))]
    #[requires(t.invariant(*f))]
    #[requires((@t.trail).len() > 0)]
    #[ensures((@(^t).trail).len() === (@t.trail).len())]
    #[ensures((^t).invariant(*f))]
    #[ensures((^self).invariant(*f))]
    #[ensures(f.eventually_sat_complete(^self) === f.eventually_sat_complete(*self))]
    #[ensures((*self).compatible(^self))]
    #[ensures(match result { 
        ClauseState::Sat => f.sat(^self),
        ClauseState::Unsat => f.unsat(^self),
        ClauseState::Unknown => !(^self).complete(),
        ClauseState::Unit => !self.complete(),
    })]
    #[ensures((self).complete() ==> *self === (^self) && ((result === ClauseState::Unsat) || f.sat(*self)))]
    pub fn unit_propagate(&mut self, f: &Formula, t: &mut Trail) -> ClauseState {
        let old_a = Ghost::record(&self);
        let old_t = Ghost::record(&t);
        let mut i: usize = 0;
        let mut out = ClauseState::Sat;
        #[invariant(ti, t.invariant(*f))]
        #[invariant(ai, self.invariant(*f))]
        #[invariant(t_len, (@(@old_t).trail).len() === (@t.trail).len())]
        #[invariant(proph, ^self === ^@old_a)]
        #[invariant(proph_t, ^t === ^@old_t)]
        #[invariant(compat, (*@old_a).compatible(*self))]
        #[invariant(maintains_sat, f.eventually_sat_complete(*@old_a) === f.eventually_sat_complete(*self))]
        #[invariant(out_not_unsat, !(out === ClauseState::Unsat))]
        #[invariant(inv, (@old_a).complete() ==> 
            *@old_a === *self && forall<j: Int> 0 <= j && j < @i ==>
             !(@f.clauses)[j].unknown(*self) && !(@f.clauses)[j].unit(*self) && (@f.clauses)[j].sat(*self)
        )]
        #[invariant(inv2,
            out === ClauseState::Sat ==> forall<j: Int> 0 <= j && j < @i ==>
             !(@f.clauses)[j].unsat(*self) && !(@f.clauses)[j].unknown(*self) && !(@f.clauses)[j].unit(*self) && (@f.clauses)[j].sat(*self)
        )]
        #[invariant(inv3,
            out === ClauseState::Unit ==> !(*@old_a).complete() 
            //&& exists<j: Int> 0 <= j && j < @i && (@f.clauses)[j].unit(*@old_a)
        )]
        #[invariant(inv4,
            out === ClauseState::Unknown ==> !self.complete()//exists<j: Int> 0 <= j && j < @i ==>
             //(@f.clauses)[j].unknown(*self)
        )]
        while i < f.clauses.len() {
            match self.unit_prop_once(i, f, t) {
                ClauseState::Sat => {},
                ClauseState::Unsat => { return ClauseState::Unsat; },
                ClauseState::Unit => { out = ClauseState::Unit; },
                ClauseState::Unknown => {
                    match out {
                        ClauseState::Sat =>
                            { out = ClauseState::Unknown; },
                        _ => {},
                    }
                }
            }
            i += 1
        }
        return out;
    }

    #[requires(f.invariant())]
    #[requires(self.invariant(*f))]
    #[requires(t.invariant(*f))]
    #[requires((@t.trail).len() > 0)]
    #[ensures((@(^t).trail).len() === (@t.trail).len())]
    #[ensures((^t).invariant(*f))]
    #[ensures((^self).invariant(*f))]
    #[ensures(f.eventually_sat_complete(*self) === f.eventually_sat_complete(^self))]
    #[ensures((*self).compatible(^self))]
    #[ensures(result === Some(false) ==> f.unsat(^self))]
    #[ensures(result === Some(true) ==> f.sat(^self))]
    #[ensures(result === None ==> !(^self).complete())]
    pub fn do_unit_propagation(&mut self, f: &Formula, t: &mut Trail) -> Option<bool> {
        let old_a = Ghost::record(&self);
        let old_t = Ghost::record(&t);
        #[invariant(ti, t.invariant(*f))]
        #[invariant(ai, self.invariant(*f))]
        #[invariant(t_len, (@(@old_t).trail).len() === (@t.trail).len())]
        #[invariant(proph_t, ^t === ^@old_t)]
        #[invariant(proph, ^self === ^@old_a)]
        #[invariant(compat, (*@old_a).compatible(*self))]
        #[invariant(maintains_sat, f.eventually_sat_complete(*@old_a) ==> f.eventually_sat_complete(*self))]
        loop {
            match self.unit_propagate(f, t) {
                ClauseState::Sat     => { return Some(true); },
                ClauseState::Unsat   => { return Some(false); },
                ClauseState::Unknown => { return None; }
                ClauseState::Unit    => { }, // Continue
            }
        } 
    }

    #[trusted] // TMP
    //#[requires(trail.trail_entries_are_assigned(*self))] // Gonna need this at some point
    #[requires(@level <= (@trail.trail).len())]
    #[requires(trail.invariant(*_f))]
    #[requires(self.invariant(*_f))]
    #[requires(@level > 0)]
    #[ensures((^trail).invariant(*_f))]
    #[ensures((^self).invariant(*_f))]
    #[ensures((@(^trail).vardata) === (@trail.vardata))]
    #[ensures((@(^trail).trail).len() === @level)]
    #[ensures(forall<j: Int> 0 <= j && j < @level ==> 
        (@(^trail).trail)[j] === (@trail.trail)[j])] // new
        /*
    #[ensures((^trail).assignments_invariant(^self))]
    #[ensures(forall<j: Int> @level <= j && j < (@trail.trail).len() ==> 
        forall<i: Int> 0 <= i && i < (@(@trail.trail)[j]).len() ==> 
            @(@(^self))[@(@(@trail.trail)[j])[i].idx] === 2)]
        //(@(^trail).trail)[j].assigned(^self))]
        */
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
        #[invariant(maintains_ass_inv, self.invariant(*_f))]
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
                    #[invariant(maintains_ass_inv2, self.invariant(*_f))]
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
        //self.1 = 0; // ADDED
    }

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