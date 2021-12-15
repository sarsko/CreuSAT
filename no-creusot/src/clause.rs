use crate::lit::*;
use crate::assignments::*;

#[derive(Debug, Clone)]
pub struct Clause(pub Vec<Lit>);

impl Clause {
    pub fn is_unsat(&self, a: &Assignments) -> bool {
        let mut i = 0;
        while i < self.0.len() {
            let lit = self.0[i];
            let res = a.0[lit.idx];
            match res {
                Some(x) => {
                    // false, false || true, true -> clause is SAT
                    if lit.polarity == x {
                        return false;
                    }
                }
                None => {
                    return false;
                } // May become SAT
            }
            i += 1;
        }
        return true;
    }
}