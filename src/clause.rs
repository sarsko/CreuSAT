extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::{
    assignments::*,
    formula::*,
    lit::*,
};

#[cfg(contracts)]
use crate::logic::{
    logic_clause::*
};

//#[derive(Debug)]
//#[derive(Clone)]
pub struct Clause {
    //pub first: Lit,
    //pub second: Lit,
    pub rest: Vec<Lit>
}

// zz#[trusted] // OKzz:
// Split up invariant and at least binary and revert to
// old invariant instead of invariant_unary_ok

impl Clone for Clause {
    // Will do last
    #[trusted] // xx#[trusted] // OKxx
    #[ensures(result === *self)]
    fn clone(&self) -> Self {
        Clause {
            rest: self.rest.clone()
        }
}
}

//#[derive(Copy, Clone, Eq)]
pub enum ClauseState {
    Sat,
    Unsat,
    Unit,
    Unknown,
    Err(usize),
}

impl Clause {
    // Better to just fix the parser. Gotta have a decent parser by delivery anyways
    #[inline]
    #[trusted] // xx#[trusted] // OKxx
    // Requires a bunch of stuff, #[trusted] // OK
    //#[ensures(result.invariant(@_f.num_vars))]
    //#[ensures((@result).len() >= 2)]
    pub fn clause_from_vec(vec: &std::vec::Vec<Lit>) -> Clause {
        Clause { rest: vec.clone() }
        /*
        Clause {
            first: vec[0],
            second: vec[1],
            rest: vec[2..].to_vec()
        }
        */
    }
}