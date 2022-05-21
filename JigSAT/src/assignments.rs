use crate::{formula::*, lit::*, trail::*};

pub type AssignedState = u8;
pub struct Assignments(pub Vec<AssignedState>);


impl Assignments {
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn set_assignment(&mut self, lit: Lit, _f: &Formula, _t: &Vec<Step>) {
        self.0[lit.index()] = lit.is_positive() as u8;
    }

    pub fn new(f: &Formula) -> Self {
        Assignments(vec![2; f.num_vars])
    }
}
