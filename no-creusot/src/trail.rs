//use crate::assignments::*;
use crate::lit::*;

#[derive(Debug, Clone, PartialEq, Eq)]
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
    pub fn enq_assignment(&mut self, l: Lit, reason: Reason) {
        let dlevel = self.trail.len() - 1;
        self.trail[dlevel].push(l);
        self.vardata[l.idx] = (dlevel, reason);
    }

    pub fn new(num_vars: usize) -> Trail {
        Trail {
            trail: vec![vec![]],
            vardata: vec![(0, Reason::Undefined); num_vars],
        }
    }
}