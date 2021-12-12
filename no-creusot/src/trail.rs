use crate::assignments::*;
use crate::lit::*;

pub struct Trail(pub Vec<Vec<Lit>>);

impl Trail {
    pub fn enq_assignment(&mut self, a: &mut Assignments, l: Lit, decisionlevel: usize) {
        //a.0[l.idx] = Some(l.polarity);
        self.0[decisionlevel].push(l);
    }
}