extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::assignments::*;
use crate::lit::*;

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
        pearlite! { (@self.vardata).len() === n }
    }

    #[predicate]
    pub fn trail_invariant(self, n: Int) -> bool {
        pearlite! { 
            forall<i: Int> 0 <= i && i < (@self.trail).len() ==>
            forall<j: Int> 0 <= j && j < (@(@self.trail)[i]).len() ==>
                @(@(@self.trail)[i])[j].idx < n 
            }
    }

    #[predicate]
    pub fn invariant(self, n: Int) -> bool {
        pearlite! {
            self.vardata_invariant(n) && self.trail_invariant(n)   
        }
    }
}

impl Trail {
    #[requires(self.invariant((@self.vardata).len()))] // (@self.vardata).len() === (@self.vardata).len() lol 
    #[requires(0 <= @lit.idx && @lit.idx < (@self.vardata).len())]
    #[requires((@self.trail).len() > 0)]
    #[ensures((^self).invariant((@self.vardata).len()))]
    #[ensures((@(^self).trail).len() === (@self.trail).len())]
    #[ensures((@(^self).vardata).len() === (@self.vardata).len())]
    //#[ensures((@(^self).vardata)[@lit.idx] === (self.trail.len() - 1usize, reason))]
    pub fn enq_assignment(&mut self, lit: Lit, reason: Reason) {
        let dlevel = self.trail.len() - 1;
        self.trail[dlevel].push(lit);
        self.vardata[lit.idx] = (dlevel, reason);
    }

    #[ensures(result.invariant(@num_vars))]
    #[ensures((@result.trail).len() === 1)]
    pub fn new(num_vars: usize) -> Trail {
        let mut vardata: Vec<(usize, Reason)> = Vec::new();
        let mut i: usize = 0;
        #[invariant(i_less, @i <= @num_vars)]
        #[invariant(len_correct, (@vardata).len() === @i)]
        while i < num_vars {
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
}