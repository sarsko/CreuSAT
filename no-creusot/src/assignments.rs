use crate::formula::*;
use crate::lit::*;
use crate::trail::*;

#[derive(Debug, Eq, PartialEq)]
pub struct Assignments(pub Vec<Option<bool>>);

impl Assignments {
    #[allow(dead_code)]
    fn clone_assignment_vector(&self) -> Vec<Option<bool>> {
        let mut out = Vec::new();
        let mut i = 0;
        while i < self.0.len() {
            let curr = self.0[i];
            out.push(curr.clone());
            i += 1;
        }
        return out;
    }

    #[allow(dead_code)]
    fn clone(&self) -> Self {
        Assignments(self.clone_assignment_vector())
    }

    pub fn set_assignment(&mut self, l: Lit) {
        if !self.0[l.idx].is_none() {
            panic!("Assignment already set. Attempting to set {:?}", l);
        }
        //assert!(self.0[l.idx].is_none());
        self.0[l.idx] = Some(l.polarity);
    }

    pub fn init_assignments(f: &Formula) -> Assignments {
        let mut assign: Vec<Option<bool>> = Vec::new();
        let mut i = 0;
        while i < f.num_vars {
            assign.push(None);
            i += 1
        }
        Assignments(assign)
    }

    pub fn find_unassigned_lit(&self) -> Option<Lit> {
        let mut i = 0;
        while i < self.0.len() {
            let curr = self.0[i];
            match curr {
                Some(_) => {} // continue
                None => {
                    return Some(Lit{ idx: i, polarity: true });
                }
            }
            i += 1;
        }
        None
    }   

    pub fn cancel_until(&mut self, trail: &mut Trail, decisionlevel: usize, level: usize) {
        let mut i: usize = decisionlevel;
        while i > level {
            let decisions = trail.trail.pop().unwrap();
            let mut j: usize = 0;
            while j < decisions.len() {
                let lit = decisions[j];
                trail.vardata[lit.idx] = (0, Reason::Undefined);
                self.0[lit.idx] = None;
                j += 1;
            }
            i -= 1;
        }
    }
}