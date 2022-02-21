use crate::lit::*;
use crate::assignments::*;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Clause(pub Vec<Lit>);

impl Clause {
    pub fn is_unsat(&self, a: &Assignments) -> bool {
        let mut i = 0;
        while i < self.0.len() {
            let lit = self.0[i];
            if lit.polarity as u8 != a.0[lit.idx] {
                return false;
            }
            i += 1;
        }
        return true;
    }
}