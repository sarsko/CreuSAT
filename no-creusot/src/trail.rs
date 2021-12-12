//use crate::assignments::*;
use crate::lit::*;

pub struct Trail(pub Vec<Vec<Lit>>);

impl Trail {
    pub fn enq_assignment(&mut self, l: Lit, decisionlevel: usize) {
        self.0[decisionlevel].push(l);
    }
}