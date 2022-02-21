use crate::lit::*;
use crate::assignments::*;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Clause(pub Vec<Lit>);

impl Clause {
    pub fn is_unsat(&self, a: &Assignments) -> bool {
        let mut i = 0;
        while i < self.0.len() {
            let lit = self.0[i];
            let ass = a.0[lit.idx];
            if ass == 2 || lit.polarity as u8 == ass {
                return false;
            }
            i += 1;
        }
        return true;
    }
}