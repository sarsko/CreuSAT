extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;

//use crate::assignments::*;
use crate::lit::*;

use crate::formula::*;

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

pub struct Trail {
    pub trail: Vec<Vec<Lit>>,
    pub vardata: Vec<(usize, Reason)>,
}

impl Trail {
    #[predicate]
    pub fn vardata_invariant(self, n: Int) -> bool {
        pearlite! { (@self.vardata).len() === n && 
            forall<i: Int> 0 <= i && i < (@self.vardata).len() ==>
        @(@self.vardata)[i].0 < (@self.trail).len() }
    }

    #[predicate]
    pub fn trail_invariant(self, f: Formula) -> bool {
        pearlite! { 
            forall<i: Int> 0 <= i && i < (@self.trail).len() ==> (
            forall<j: Int> 0 <= j && j < (@(@self.trail)[i]).len() ==>
                0 <= @(@(@self.trail)[i])[j].idx && @(@(@self.trail)[i])[j].idx < @f.num_vars )
            }
    }

    #[predicate]
    pub fn invariant(self, f: Formula) -> bool {
        pearlite! {
            self.vardata_invariant(@f.num_vars) && self.trail_invariant(f) &&  
            forall<j: Int> 0 <= j && j < (@self.vardata).len() ==>
            match (@self.vardata)[j].1 {
                Reason::Undefined => true,
                Reason::Decision => true,
                Reason::Unit => true,
                Reason::Long(k) => 0 <= @k && @k < (@f.clauses).len(),
            }
        }
    }
}

impl Trail {
    #[trusted] // Seems like the match reason makes it not check out. Talk to Xavier about it?
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

    #[trusted] // Checks out
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

    #[trusted] // new
    #[requires(self.invariant(*_f))]
    #[ensures((^self).invariant(*_f))] // Doesn't check out. Cant understand what I'm missing
    #[ensures((@self.vardata) === (@(^self).vardata))]
    #[ensures(forall<i: Int> 0 <= i && i < (@self.trail).len() ==>
        (@self.trail)[i] === (@(^self).trail)[i])]
    #[ensures((@(^self).trail).len() === (@self.trail).len() + 1)]
    #[ensures((@(@(^self).trail)[(@self.trail).len()]).len() === 0)]
    pub fn add_level(&mut self, _f: &Formula) {
        self.trail.push(Vec::new());
    }
}