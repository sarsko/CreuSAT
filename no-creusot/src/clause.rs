use crate::lit::*;
use crate::assignments::*;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Clause {
    pub first: Lit,
    pub second: Lit,
    pub rest: Vec<Lit>
}

impl Clause {
    #[inline]
    pub fn clause_from_vec(vec: &Vec<Lit>) -> Clause {
        Clause {
            first: vec[0],
            second: vec[1],
            rest: vec[2..].to_vec()
        }
    }
    pub fn is_unsat(&self, a: &Assignments) -> bool {
        if self.first.polarity as u8 != a.0[self.first.idx] {
            return false;
        }
        if self.second.polarity as u8 != a.0[self.second.idx] {
            return false;
        }
        let mut i = 0;
        while i < self.rest.len() {
            let lit = &self.rest[i];
            if lit.polarity as u8 != a.0[lit.idx] {
                return false;
            }
            i += 1;
        }
        return true;
    }
}